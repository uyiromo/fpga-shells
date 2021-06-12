// See LICENSE for license details.
package sifive.fpgashells.devices.xilinx.xilinxvc707mig

import Chisel._
import chisel3.experimental.{Analog,attach, withClockAndReset}
import chisel3.core.dontTouch
import freechips.rocketchip.amba.axi4._
import freechips.rocketchip.config.Parameters
import freechips.rocketchip.subsystem._
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.interrupts._
import sifive.fpgashells.ip.xilinx.vc707mig.{VC707MIGIOClocksReset, VC707MIGIODDR, vc707mig}
import freechips.rocketchip.util._

import sifive.fpgashells.ip.xilinx.Series7MMCM
import sifive.fpgashells.clocks._
import sifive.blocks.devices.nvmmctr._
import nvsit._

case class XilinxVC707MIGParams(
  address : Seq[AddressSet]
)

class XilinxVC707MIGPads(depth : BigInt) extends VC707MIGIODDR(depth) {
  def this(c : XilinxVC707MIGParams) {
    this(AddressRange.fromSets(c.address).head.size)
  }
}

class XilinxVC707MIGIO(depth : BigInt) extends VC707MIGIODDR(depth) with VC707MIGIOClocksReset
{
  val lat_cr                = Bits(INPUT,  8)
  val lat_cw                = Bits(INPUT,  8)
  val lat_dr256             = Bits(INPUT,  8)
  val lat_dr4096            = Bits(INPUT,  8)
  val lat_dw256             = Bits(INPUT,  8)
  val lat_dw4096            = Bits(INPUT,  8)
  val cnt_read              = Bits(OUTPUT, 64)
  val cnt_write             = Bits(OUTPUT, 64)
  val cnt_bdr               = Bits(OUTPUT, 64)
  val cnt_bdw               = Bits(OUTPUT, 64)
}

class XilinxVC707MIGIsland(c : XilinxVC707MIGParams, val crossing: ClockCrossingType = AsynchronousCrossing(8))(implicit p: Parameters) extends LazyModule with CrossesToOnlyOneClockDomain {
  val ranges = AddressRange.fromSets(c.address)
  require (ranges.size == 1, "DDR range must be contiguous")
  val offset = ranges.head.base
  val depth = ranges.head.size
  require((depth<=0x100000000L),"vc707mig supports upto 4GB depth configuraton")
  
  val device = new MemoryDevice
  val node = AXI4SlaveNode(Seq(AXI4SlavePortParameters(
      slaves = Seq(AXI4SlaveParameters(
      address       = c.address,
      resources     = device.reg,
      regionType    = RegionType.UNCACHED,
      executable    = true,
      supportsWrite = TransferSizes(1, 64),
      supportsRead  = TransferSizes(1, 64))),
    beatBytes = 8)))

  lazy val module = new LazyRawModuleImp(this) {
    val io = IO(new Bundle {
      val port = new XilinxVC707MIGIO(depth)
    })

    childClock := io.port.ui_clk
    childReset := io.port.ui_clk_sync_rst

    //MIG black box instantiation
    val blackbox = Module(new vc707mig(depth))
    val (axi_async, _) = node.in(0)

    //pins to top level

    //inouts
    attach(io.port.ddr3_dq,blackbox.io.ddr3_dq)
    attach(io.port.ddr3_dqs_n,blackbox.io.ddr3_dqs_n)
    attach(io.port.ddr3_dqs_p,blackbox.io.ddr3_dqs_p)

    //outputs
    io.port.ddr3_addr         := blackbox.io.ddr3_addr
    io.port.ddr3_ba           := blackbox.io.ddr3_ba
    io.port.ddr3_ras_n        := blackbox.io.ddr3_ras_n
    io.port.ddr3_cas_n        := blackbox.io.ddr3_cas_n
    io.port.ddr3_we_n         := blackbox.io.ddr3_we_n
    io.port.ddr3_reset_n      := blackbox.io.ddr3_reset_n
    io.port.ddr3_ck_p         := blackbox.io.ddr3_ck_p
    io.port.ddr3_ck_n         := blackbox.io.ddr3_ck_n
    io.port.ddr3_cke          := blackbox.io.ddr3_cke
    io.port.ddr3_cs_n         := blackbox.io.ddr3_cs_n
    io.port.ddr3_dm           := blackbox.io.ddr3_dm
    io.port.ddr3_odt          := blackbox.io.ddr3_odt

    //inputs
    //NO_BUFFER clock
    blackbox.io.sys_clk_i     := io.port.sys_clk_i

    io.port.ui_clk            := blackbox.io.ui_clk
    io.port.ui_clk_sync_rst   := blackbox.io.ui_clk_sync_rst
    io.port.mmcm_locked       := blackbox.io.mmcm_locked
    blackbox.io.aresetn       := io.port.aresetn
    blackbox.io.app_sr_req    := Bool(false)
    blackbox.io.app_ref_req   := Bool(false)
    blackbox.io.app_zq_req    := Bool(false)
    //app_sr_active           := unconnected
    //app_ref_ack             := unconnected
    //app_zq_ack              := unconnected

    //misc
    io.port.init_calib_complete := blackbox.io.init_calib_complete
    blackbox.io.sys_rst         := io.port.sys_rst
    //mig.device_temp           := unconnceted

    val awaddr = axi_async.aw.bits.addr - UInt(offset)
    val araddr = axi_async.ar.bits.addr - UInt(offset)

    // latency control
    val nvmmctr = withClockAndReset(io.port.sys_clk_i.asClock, io.port.sys_rst){
      Module(new NVMMCTRModule())
    }

    // Clock for MPE
    val mpe_pll = Module(new Series7MMCM(PLLParameters(
      "mpePLL",
      PLLInClockParameters(200),     // Input: 200 MHz
      Seq(
        PLLOutClockParameters(50)   // Output 100 MHz
      )
    )))
    mpe_pll.io.clk_in1  := io.port.sys_clk_i.asClock
    mpe_pll.io.reset    := io.port.sys_rst

    // aliases
    val sysClk = io.port.sys_clk_i.asClock
    val sysRst = io.port.sys_rst | childReset
    val mpeClk = mpe_pll.io.clk_out1.get
    val mpeRst = !mpe_pll.io.locked | io.port.sys_rst | childReset

    // Memory Protection Engine
    val mpe = withClockAndReset(mpeClk, mpeRst){ Module(new MPE(4)) }


    // connections
    // axi_async <--> MPE <--> NVMMCTR(delay) <--> MIG (blackbox)

    /*
     * axi_async <--> MPE
     */
    withClockAndReset(sysClk, sysRst){
      val idBits  = 4
      val dataBits = 64
      val queueAR = genAsyncQueue(new AXI4BusA(idBits),           sysClk, sysRst, mpeClk, mpeRst)
      val queueR  = genAsyncQueue(new AXI4BusR(idBits, dataBits), mpeClk, mpeRst, sysClk, sysRst)
      val queueAW = genAsyncQueue(new AXI4BusA(idBits),           sysClk, sysRst, mpeClk, mpeRst)
      val queueW  = genAsyncQueue(new AXI4BusW(dataBits),         sysClk, sysRst, mpeClk, mpeRst)
      val queueB  = genAsyncQueue(new AXI4BusB(idBits),           mpeClk, mpeRst, sysClk, sysRst)

      queueAR.io.enq <> axi_async.ar
      mpe.io.cpu.ar  <> queueAR.io.deq
      //queueAR.io.enq.bits.addr := araddr
      queueAR.io.enq.bits.addr := araddr(31, 6)

      queueR.io.enq <> mpe.io.cpu.r
      axi_async.r   <> queueR.io.deq

      queueAW.io.enq <> axi_async.aw
      mpe.io.cpu.aw  <> queueAW.io.deq
      //queueAW.io.enq.bits.addr := awaddr
      queueAW.io.enq.bits.addr := awaddr(31, 6)

      queueW.io.enq <> axi_async.w
      mpe.io.cpu.w  <> queueW.io.deq

      queueB.io.enq <> mpe.io.cpu.b
      axi_async.b   <> queueB.io.deq
    }

    /*
     * MPE <--> NVMMCTR <--> MIG
     */
    withClockAndReset(sysClk, sysRst){
      val idBits  = 4
      val dataBits = 512
      val queueAR = genAsyncQueue(new AXI4BusAS(idBits),           mpeClk, mpeRst, sysClk, sysRst)
      val queueR  = genAsyncQueue(new AXI4BusRS(idBits, dataBits), sysClk, sysRst, mpeClk, mpeRst)
      val queueAW = genAsyncQueue(new AXI4BusAS(idBits),           mpeClk, mpeRst, sysClk, sysRst)
      val queueW  = genAsyncQueue(new AXI4BusWS(dataBits),         mpeClk, mpeRst, sysClk, sysRst)
      val queueB  = genAsyncQueue(new AXI4BusB(idBits),           sysClk, sysRst, mpeClk, mpeRst)

      // AR except for valid/ready
      queueAR.io.enq <> mpe.io.mem.ar
      blackbox.io.s_axi_arid    := queueAR.io.deq.bits.id
      //blackbox.io.s_axi_araddr  := queueAR.io.deq.bits.addr
      blackbox.io.s_axi_araddr  := Cat(queueAR.io.deq.bits.addr, 0.U(6.W))
      blackbox.io.s_axi_arlen   := 0.U(8.W)     // 1 beat
      blackbox.io.s_axi_arsize  := 6.U(3.W)     // 2**6 bytes/beat
      blackbox.io.s_axi_arburst := "b01".U(2.W) // INCR burst
      //blackbox.io.s_axi_arlock  := unconnected
      //blackbox.io.s_axi_arcache := unconnected
      //blackbox.io.s_axi_arprot  := unconnected
      //blackbox.io.s_axi_arqos   := unconnected

      // R
      mpe.io.mem.r <> queueR.io.deq
      queueR.io.enq.bits.id    := blackbox.io.s_axi_rid
      queueR.io.enq.bits.data  := blackbox.io.s_axi_rdata
      queueR.io.enq.bits.resp  := blackbox.io.s_axi_rresp
      //queueR.io.enq.bits.last  := blackbox.io.s_axi_rlast
      queueR.io.enq.valid      := blackbox.io.s_axi_rvalid
      blackbox.io.s_axi_rready := queueR.io.enq.ready

      // AW except for valid/ready
      queueAW.io.enq <> mpe.io.mem.aw
      blackbox.io.s_axi_awid    := queueAW.io.deq.bits.id
      //blackbox.io.s_axi_awaddr  := queueAW.io.deq.bits.addr
      blackbox.io.s_axi_awaddr  := Cat(queueAW.io.deq.bits.addr, 0.U(6.W))
      blackbox.io.s_axi_awlen   := 0.U(8.W)     // 1 beat
      blackbox.io.s_axi_awsize  := 6.U(3.W)     // 2**6 bytes/beat
      blackbox.io.s_axi_awburst := "b01".U(2.W) // INCR burst
      //blackbox.io.s_axi_awlock  := unconnected
      //blackbox.io.s_axi_awcache := unconnected
      //blackbox.io.s_axi_awprot  := unconnected
      //blackbox.io.s_axi_awqos   := unconnected

      // W
      queueW.io.enq <> mpe.io.mem.w
      blackbox.io.s_axi_wdata  := queueW.io.deq.bits.data
      //blackbox.io.s_axi_wstrb  := queueW.io.deq.bits.strb
      //blackbox.io.s_axi_wlast  := queueW.io.deq.bits.last
      blackbox.io.s_axi_wstrb  := "xFFFFFFFFFFFFFFFF".U(64.W)
      blackbox.io.s_axi_wlast  := true.B  // only 1 beat
      blackbox.io.s_axi_wvalid := queueW.io.deq.valid
      queueW.io.deq.ready      := blackbox.io.s_axi_wready

      // B
      mpe.io.mem.b <> queueB.io.deq
      queueB.io.enq.bits.id     := blackbox.io.s_axi_bid
      queueB.io.enq.bits.resp   := blackbox.io.s_axi_bresp
      queueB.io.enq.valid       := blackbox.io.s_axi_bvalid
      blackbox.io.s_axi_bready  := queueB.io.enq.ready


      /*
       * nvmmctr
       */
      // AR (queue <--> nvmmctr)
      nvmmctr.io.mbus_arvalid := queueAR.io.deq.valid
      queueAR.io.deq.ready    := nvmmctr.io.mbus_arready
      nvmmctr.io.mbus_araddr  := queueAR.io.deq.bits.addr

      // AW (queue <--> nvmmctr)
      nvmmctr.io.mbus_awvalid := queueAW.io.deq.valid
      queueAW.io.deq.ready    := nvmmctr.io.mbus_awready
      nvmmctr.io.mbus_awaddr  := queueAW.io.deq.bits.addr

      // AR (nvmmctr <--> MIG)
      blackbox.io.s_axi_arvalid := nvmmctr.io.mig_arvalid
      nvmmctr.io.mig_arready    := blackbox.io.s_axi_arready

      // AW (nvmmctr <--> MIG)
      blackbox.io.s_axi_awvalid := nvmmctr.io.mig_awvalid
      nvmmctr.io.mig_awready    := blackbox.io.s_axi_awready
    }

    //nvmmctr.io.clear          := false.B
    nvmmctr.io.nvmm_begin     := io.port.nvmm_begin
    nvmmctr.io.lat_cr         := io.port.lat_cr
    nvmmctr.io.lat_cw         := io.port.lat_cw
    nvmmctr.io.lat_dr256      := io.port.lat_dr256
    nvmmctr.io.lat_dr4096     := io.port.lat_dr4096
    nvmmctr.io.lat_dw256      := io.port.lat_dw256
    nvmmctr.io.lat_dw4096     := io.port.lat_dw4096
    io.port.cnt_read          := nvmmctr.io.cnt_read
    io.port.cnt_write         := nvmmctr.io.cnt_write
    io.port.cnt_bdr           := nvmmctr.io.cnt_bdr
    io.port.cnt_bdw           := nvmmctr.io.cnt_bdw

    blackbox.io.nvmm_begin    := io.port.nvmm_begin
    blackbox.io.tRCD2         := io.port.tRCD2
    blackbox.io.tRP2          := io.port.tRP2
    blackbox.io.tRAS2         := io.port.tRAS2
    io.port.cnt_act           := blackbox.io.cnt_act

    //dontTouch(nvmmctr.io)
    //dontTouch(io.port)

  }

  // helpers
  def genAsyncQueue[T <: Bundle](gen: T, enq_clk: Clock, enq_rst: Bool,
    deq_clk: Clock, deq_rst: Bool) = {
    val q = Module(new AsyncQueue(gen, AsyncQueueParams(depth = 2)))
    q.io.enq_clock := enq_clk
    q.io.enq_reset := enq_rst
    q.io.deq_clock := deq_clk
    q.io.deq_reset := deq_rst

    q
  }






}

class XilinxVC707MIG(c : XilinxVC707MIGParams, crossing: ClockCrossingType = AsynchronousCrossing(8))(implicit p: Parameters) extends LazyModule {
  val ranges = AddressRange.fromSets(c.address)
  val depth = ranges.head.size

  val buffer  = LazyModule(new TLBuffer)
  val toaxi4  = LazyModule(new TLToAXI4(adapterName = Some("mem"), stripBits = 1))
  val indexer = LazyModule(new AXI4IdIndexer(idBits = 4))
  val deint   = LazyModule(new AXI4Deinterleaver(p(CacheBlockBytes)))
  val yank    = LazyModule(new AXI4UserYanker)
  val island  = LazyModule(new XilinxVC707MIGIsland(c, crossing))

  val node: TLInwardNode =
    island.crossAXI4In(island.node) := yank.node := deint.node := indexer.node := toaxi4.node := buffer.node

  lazy val module = new LazyModuleImp(this) {
    val io = IO(new Bundle {
      val port = new XilinxVC707MIGIO(depth)
    })

    io.port <> island.module.io.port
    dontTouch(io.port)
  }
}
