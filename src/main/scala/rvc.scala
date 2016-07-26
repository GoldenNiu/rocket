package rocket

import Chisel._
import Chisel.ImplicitConversions._
import Util._
import cde.Parameters

object RVCExpander {
  def rs1p(x: UInt) = Cat(UInt(1,2), x(9,7))
  def rs2p(x: UInt) = Cat(UInt(1,2), x(4,2))
  def rs2(x: UInt) = x(6,2)
  def rd(x: UInt) = x(11,7)
  def addi4spnImm(x: UInt) = Cat(x(10,7), x(12,11), x(5), x(6), UInt(0,2))
  def lwImm(x: UInt) = Cat(x(5), x(12,10), x(6), UInt(0,2))
  def ldImm(x: UInt) = Cat(x(6,5), x(12,10), UInt(0,3))
  def lwspImm(x: UInt) = Cat(x(3,2), x(12), x(6,4), UInt(0,2))
  def ldspImm(x: UInt) = Cat(x(4,2), x(12), x(6,5), UInt(0,3))
  def swspImm(x: UInt) = Cat(x(8,7), x(12,9), UInt(0,2))
  def sdspImm(x: UInt) = Cat(x(9,7), x(12,10), UInt(0,3))
  def luiImm(x: UInt) = Cat(Fill(15, x(12)), x(6,2), UInt(0,12))
  def addi16spImm(x: UInt) = Cat(Fill(3, x(12)), x(4,3), x(5), x(2), x(6), UInt(0,4))
  def addiImm(x: UInt) = Cat(Fill(7, x(12)), x(6,2))
  def jImm(x: UInt) = Cat(Fill(10, x(12)), x(8), x(10,9), x(6), x(7), x(2), x(11), x(5,3), UInt(0,1))
  def bImm(x: UInt) = Cat(Fill(5, x(12)), x(6,5), x(2), x(11,10), x(4,3), UInt(0,1))
  def shamt(x: UInt) = Cat(x(12), x(6,2))
  def sp = UInt(2,5)
  def x0 = UInt(0,5)

  def q0(x: UInt)(implicit p: Parameters) = {
    def addi4spn = {
      val opc = Mux(x(12,5).orR, UInt(0x13,7), UInt(0x1F,7))
      Cat(addi4spnImm(x), sp, UInt(0,3), rs2p(x), opc)
    }
    def ld = Cat(ldImm(x), rs1p(x), UInt(3,3), rs2p(x), UInt(0x03,7))
    def lw = Cat(lwImm(x), rs1p(x), UInt(2,3), rs2p(x), UInt(0x03,7))
    def fld = Cat(ldImm(x), rs1p(x), UInt(3,3), rs2p(x), UInt(0x07,7))
    def flw = {
      if (p(XLen) == 32) Cat(lwImm(x), rs1p(x), UInt(2,3), rs2p(x), UInt(0x07,7))
      else ld
    }
    def unimp = Cat(lwImm(x) >> 5, rs2p(x), rs1p(x), UInt(2,3), lwImm(x)(4,0), UInt(0x2F,7))
    def sd = Cat(ldImm(x) >> 5, rs2p(x), rs1p(x), UInt(3,3), ldImm(x)(4,0), UInt(0x23,7))
    def sw = Cat(lwImm(x) >> 5, rs2p(x), rs1p(x), UInt(2,3), lwImm(x)(4,0), UInt(0x23,7))
    def fsd = Cat(ldImm(x) >> 5, rs2p(x), rs1p(x), UInt(3,3), ldImm(x)(4,0), UInt(0x27,7))
    def fsw = {
      if (p(XLen) == 32) Cat(lwImm(x) >> 5, rs2p(x), rs1p(x), UInt(2,3), lwImm(x)(4,0), UInt(0x27,7))
      else sd
    }
    Seq(addi4spn, fld, lw, flw, unimp, fsd, sw, fsw)
  }

  def q1(x: UInt)(implicit p: Parameters) = {
    def addi = Cat(addiImm(x), rd(x), UInt(0,3), rd(x), UInt(0x13,7))
    def addiw = {
      val opc = Mux(rd(x).orR, UInt(0x1B,7), UInt(0x1F,7))
      Cat(addiImm(x), rd(x), UInt(0,3), rd(x), opc)
    }
    def jal = {
      if (p(XLen) == 32) j | UInt(1 << 7)
      else addiw
    }
    def li = Cat(addiImm(x), x0, UInt(0,3), rd(x), UInt(0x13,7))
    def addi16sp = {
      val opc = Mux(addiImm(x).orR, UInt(0x13,7), UInt(0x1F,7))
      Cat(addi16spImm(x), rd(x), UInt(0,3), rd(x), opc)
    }
    def lui = {
      val opc = Mux(addiImm(x).orR, UInt(0x37,7), UInt(0x3F,7))
      val insn = Cat(luiImm(x)(31,12), rd(x), opc)
      Mux(rd(x) === x0 || rd(x) === sp, addi16sp, insn)
    }
    def j = Cat(jImm(x)(20), jImm(x)(10,1), jImm(x)(11), jImm(x)(19,12), x0, UInt(0x6F,7))
    def beqz = Cat(bImm(x)(12), bImm(x)(10,5), x0, rs1p(x), UInt(0,3), bImm(x)(4,1), bImm(x)(11), UInt(0x63,7))
    def bnez = beqz | UInt(1 << 12)
    def arith = {
      def srli = Cat(shamt(x), rs1p(x), UInt(5,3), rs1p(x), UInt(0x13,7))
      def srai = srli | UInt(1 << 30)
      def andi = Cat(addiImm(x), rs1p(x), UInt(7,3), rs1p(x), UInt(0x13,7))
      def rtype = {
        val funct = Seq(0.U, 4.U, 6.U, 7.U, 0.U, 0.U, 2.U, 3.U)(Cat(x(12), x(6,5)))
        val sub = Mux(x(6,5) === UInt(0), UInt(1 << 30), UInt(0))
        val opc = Mux(x(12), UInt(0x3B,7), UInt(0x33,7))
        Cat(rs2p(x), rs1p(x), funct, rs1p(x), opc) | sub
      }
      Seq(srli, srai, andi, rtype)(x(11,10))
    }
    Seq(addi, jal, li, lui, arith, j, beqz, bnez)
  }
  
  def q2(x: UInt)(implicit p: Parameters) = {
    def slli = Cat(shamt(x), rd(x), UInt(1,3), rd(x), UInt(0x13,7))
    def ldsp = Cat(ldspImm(x), sp, UInt(3,3), rd(x), UInt(0x03,7))
    def lwsp = Cat(lwspImm(x), sp, UInt(2,3), rd(x), UInt(0x03,7))
    def fldsp = Cat(ldspImm(x), sp, UInt(3,3), rd(x), UInt(0x07,7))
    def flwsp = {
      if (p(XLen) == 32) Cat(lwspImm(x), sp, UInt(2,3), rd(x), UInt(0x07,7))
      else ldsp
    }
    def sdsp = Cat(sdspImm(x) >> 5, rs2(x), sp, UInt(3,3), sdspImm(x)(4,0), UInt(0x23,7))
    def swsp = Cat(swspImm(x) >> 5, rs2(x), sp, UInt(2,3), swspImm(x)(4,0), UInt(0x23,7))
    def fsdsp = Cat(sdspImm(x) >> 5, rs2(x), sp, UInt(3,3), sdspImm(x)(4,0), UInt(0x27,7))
    def fswsp = {
      if (p(XLen) == 32) Cat(swspImm(x) >> 5, rs2(x), sp, UInt(2,3), swspImm(x)(4,0), UInt(0x27,7))
      else sdsp
    }
    def jalr = {
      val mv = Cat(rs2(x), x0, UInt(0,3), rd(x), UInt(0x33,7))
      val add = mv | (rd(x) << 15)
      val jr = Cat(rs2(x), rd(x), UInt(0,3), x0, UInt(0x67,7))
      val reserved = Cat(jr >> 7, UInt(0x1F,7))
      val jr_reserved = Mux(rd(x).orR, jr, reserved)
      val jr_mv = Mux(rs2(x).orR, mv, jr_reserved)
      val jalr = jr | UInt(1 << 7)
      val ebreak = Cat(jr >> 7, UInt(0x73,7)) | UInt(1 << 20)
      val jalr_ebreak = Mux(rd(x).orR, jalr, ebreak)
      val jalr_add = Mux(rs2(x).orR, add, jalr_ebreak)
      Mux(x(12), jalr_add, jr_mv)
    }
    Seq(slli, fldsp, lwsp, flwsp, jalr, fsdsp, swsp, fswsp)
  }

  def q3(x: UInt) = Seq.fill(8)(x)

  def apply(x: UInt)(implicit p: Parameters) = {
    val s = q0(x) ++ q1(x) ++ q2(x) ++ q3(x)
    s(Cat(x(1,0), x(15,13)))
  }
}

class RVCExpander(implicit p: Parameters) extends Module {
  val io = new Bundle {
    val in = UInt(INPUT, 32)
    val out = UInt(OUTPUT, 32)
    val rvc = Bool(OUTPUT)
  }
  io.rvc := io.in(1,0) =/= UInt(3)
  io.out := RVCExpander(io.in)
}
