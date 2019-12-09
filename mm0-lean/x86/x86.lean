import x86.bits logic.relation

namespace x86
local notation `S` := bitvec.singleton

@[reducible] def regnum := bitvec 4

def RAX : regnum := 0
def RCX : regnum := 1
def RDX : regnum := 2
def RSP : regnum := 4
def RBP : regnum := 5
def RSI : regnum := 6
def RDI : regnum := 7

def REX := option (bitvec 4)

def REX.to_nat : REX → ℕ
| none := 0
| (some r) := r.to_nat

def REX.W (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 3)
def REX.R (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 2)
def REX.X (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 1)
def REX.B (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 0)

def rex_reg (b : bool) (r : bitvec 3) : regnum := (bitvec.append r (S b) : _)

structure scale_index :=
(scale : bitvec 2)
(index : regnum)

inductive base | none | rip | reg (reg : regnum)

inductive RM : Type
| reg : regnum → RM
| mem : option scale_index → base → qword → RM

def RM.is_mem : RM → Prop
| (RM.mem _ _ _) := true
| _ := false

@[reducible] def Mod := bitvec 2

inductive read_displacement : Mod → qword → list byte → Prop
| disp0 : read_displacement 0 0 []
| disp8 (b : byte) : read_displacement 1 (EXTS b) [b]
| disp32 (w : word) (l) : w.to_list_byte l → read_displacement 2 (EXTS w) l

def read_sib_displacement (mod : Mod) (bbase : regnum) (w : qword)
  (Base : base) (l : list byte) : Prop :=
if bbase = RBP ∧ mod = 0 then
  ∃ b, w = EXTS b ∧ Base = base.none ∧ l = [b]
else read_displacement mod w l ∧ Base = base.reg bbase

inductive read_SIB (rex : REX) (mod : Mod) : RM → list byte → Prop
| mk (b : byte) (bs ix SS) (disp bbase' l) :
  split_bits b.to_nat [⟨3, bs⟩, ⟨3, ix⟩, ⟨2, SS⟩] →
  let bbase := rex_reg rex.B bs,
      index := rex_reg rex.X ix,
      scaled_index : option scale_index :=
        if index = RSP then none else some ⟨SS, index⟩ in
  read_sib_displacement mod bbase disp bbase' l →
  read_SIB (RM.mem scaled_index bbase' disp) (b :: l)

inductive read_ModRM (rex : REX) : regnum → RM → list byte → Prop
| imm32 (b : byte) (reg_opc : bitvec 3) (i : word) (disp) :
  split_bits b.to_nat [⟨3, 0b101⟩, ⟨3, reg_opc⟩, ⟨2, 0b00⟩] →
  i.to_list_byte disp →
  read_ModRM (rex_reg rex.R reg_opc)
    (RM.mem none base.rip (EXTS i)) (b :: disp)
| reg (b : byte) (rm reg_opc : bitvec 3) :
  split_bits b.to_nat [⟨3, rm⟩, ⟨3, reg_opc⟩, ⟨2, 0b11⟩] →
  read_ModRM (rex_reg rex.R reg_opc) (RM.reg (rex_reg rex.B rm)) [b]
| sib (b : byte) (reg_opc : bitvec 3) (mod : Mod) (sib) (l) :
  split_bits b.to_nat [⟨3, 0b100⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩] →
  read_SIB rex mod sib l →
  read_ModRM (rex_reg rex.R reg_opc) sib (b :: l)
| mem (b : byte) (rm reg_opc : bitvec 3) (mod : Mod) (disp l) :
  split_bits b.to_nat [⟨3, rm⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩] → rm ≠ 0b100 →
  ¬ (rm = 0b101 ∧ mod = 0b00) →
  read_displacement mod disp l →
  read_ModRM (rex_reg rex.R reg_opc)
    (RM.mem none (base.reg (rex_reg rex.B rm)) disp) (b :: l)

inductive read_opcode_ModRM (rex : REX) : bitvec 3 → RM → list byte → Prop
| mk (rn : regnum) (rm l v b) :
  read_ModRM rex rn rm l →
  split_bits rn.to_nat [⟨3, v⟩, ⟨1, b⟩] →
  read_opcode_ModRM v rm l

-- obsolete group 1-4 prefixes omitted
inductive read_prefixes : REX → list byte → Prop
| nil : read_prefixes none []
| rex (b : byte) (rex) :
  split_bits b.to_nat [⟨4, rex⟩, ⟨4, 0b0100⟩] →
  read_prefixes (some rex) [b]

@[derive decidable_eq]
inductive wsize
| Sz8 (have_rex : bool)
| Sz16 | Sz32 | Sz64
open wsize

def wsize.to_nat : wsize → ℕ
| (Sz8 _) := 8
| Sz16 := 16
| Sz32 := 32
| Sz64 := 64

inductive read_imm8 : qword → list byte → Prop
| mk (b : byte) : read_imm8 (EXTS b) [b]

inductive read_imm16 : qword → list byte → Prop
| mk (w : bitvec 16) (l) : bits_to_byte 2 w l → read_imm16 (EXTS w) l

inductive read_imm32 : qword → list byte → Prop
| mk (w : word) (l) : w.to_list_byte l → read_imm32 (EXTS w) l

def read_imm : wsize → qword → list byte → Prop
| (Sz8 _) := read_imm8
| Sz16 := read_imm16
| Sz32 := read_imm32
| Sz64 := λ _ _, false

def read_full_imm : wsize → qword → list byte → Prop
| (Sz8 _) := read_imm8
| Sz16 := read_imm16
| Sz32 := read_imm32
| Sz64 := λ w l, w.to_list_byte l

def op_size (have_rex w v : bool) : wsize :=
if ¬ v then Sz8 have_rex else
if w then Sz64 else
-- if override then Sz16 else
Sz32

def op_size_W (rex : REX) : bool → wsize := op_size rex.is_some rex.W

inductive dest_src
| Rm_i : RM → qword → dest_src
| Rm_r : RM → regnum → dest_src
| R_rm : regnum → RM → dest_src
open dest_src

inductive imm_rm
| rm : RM → imm_rm
| imm : qword → imm_rm

inductive unop | dec | inc | not | neg

inductive binop
| add | or  | adc | sbb | and | sub | xor | cmp
| rol | ror | rcl | rcr | shl | shr | tst | sar

inductive binop.bits : binop → bitvec 4 → Prop
| add : binop.bits binop.add 0x0
| or  : binop.bits binop.or  0x1
| adc : binop.bits binop.adc 0x2
| sbb : binop.bits binop.sbb 0x3
| and : binop.bits binop.and 0x4
| sub : binop.bits binop.sub 0x5
| xor : binop.bits binop.xor 0x6
| cmp : binop.bits binop.cmp 0x7
| rol : binop.bits binop.rol 0x8
| ror : binop.bits binop.ror 0x9
| rcl : binop.bits binop.rcl 0xa
| rcr : binop.bits binop.rcr 0xb
| shl : binop.bits binop.shl 0xc
| shr : binop.bits binop.shr 0xd
| tst : binop.bits binop.tst 0xe
| sar : binop.bits binop.sar 0xf

inductive basic_cond
| o | b | e | na | s | l | ng

inductive basic_cond.bits : basic_cond → bitvec 3 → Prop
| o  : basic_cond.bits basic_cond.o  0x0
| b  : basic_cond.bits basic_cond.b  0x1
| e  : basic_cond.bits basic_cond.e  0x2
| na : basic_cond.bits basic_cond.na 0x3
| s  : basic_cond.bits basic_cond.s  0x4
| l  : basic_cond.bits basic_cond.l  0x6
| ng : basic_cond.bits basic_cond.ng 0x7

inductive cond_code
| always
| pos : basic_cond → cond_code
| neg : basic_cond → cond_code

def cond_code.mk : bool → basic_cond → cond_code
| ff := cond_code.pos
| tt := cond_code.neg

inductive cond_code.bits : cond_code → bitvec 4 → Prop
| mk (v : bitvec 4) (b c code) :
  split_bits v.to_nat [⟨3, c⟩, ⟨1, S b⟩] →
  basic_cond.bits code c →
  cond_code.bits (cond_code.mk b code) v

inductive ast
| unop : unop → wsize → RM → ast
| binop : binop → wsize → dest_src → ast
| mul : wsize → RM → ast
| div : wsize → RM → ast
| lea : wsize → dest_src → ast

| movsx : wsize → dest_src → wsize → ast
| movzx : wsize → dest_src → wsize → ast
| xchg : wsize → RM → regnum → ast
| cmpxchg : wsize → RM → regnum → ast
| xadd : wsize → RM → regnum → ast
| cmov : cond_code → wsize → dest_src → ast
| setcc : cond_code → bool → RM → ast

| jump : RM → ast
| jcc : cond_code → qword → ast
| call : imm_rm → ast
| ret : qword → ast
| push : imm_rm → ast
| pop : RM → ast
| leave : ast

| cmc
| clc
| stc
-- | int : byte → ast
| syscall

def ast.mov := ast.cmov cond_code.always

inductive decode_hi (v : bool) (sz : wsize) (r : RM) :
  bool → bitvec 3 → ast → list byte → Prop
| test (imm l) : read_imm sz imm l →
  decode_hi ff 0b000 (ast.binop binop.tst sz (Rm_i r imm)) l
| not : decode_hi ff 0b010 (ast.unop unop.not sz r) []
| neg : decode_hi ff 0b011 (ast.unop unop.neg sz r) []
| mul : decode_hi ff 0b100 (ast.mul sz r) []
| div : decode_hi ff 0b110 (ast.div sz r) []
| inc : decode_hi tt 0b000 (ast.unop unop.inc sz r) []
| dec : decode_hi tt 0b001 (ast.unop unop.dec sz r) []
| call : v → decode_hi tt 0b010 (ast.call (imm_rm.rm r)) []
| jump : v → decode_hi tt 0b100 (ast.jump r) []
| push : v → decode_hi tt 0b110 (ast.push (imm_rm.rm r)) []

inductive decode_two (rex : REX) : ast → list byte → Prop
| cmov (b : byte) (c reg r l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x4⟩] →
  let sz := op_size tt rex.W tt in
  read_ModRM rex reg r l →
  cond_code.bits code c →
  decode_two (ast.cmov code sz (R_rm reg r)) (b :: l)
| jcc (b : byte) (c imm l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x8⟩] →
  read_imm32 imm l →
  cond_code.bits code c →
  decode_two (ast.jcc code imm) (b :: l)
| setcc (b : byte) (c reg r l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x9⟩] →
  read_ModRM rex reg r l →
  cond_code.bits code c →
  decode_two (ast.setcc code rex.is_some r) (b :: l)
| cmpxchg (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1011000⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  decode_two (ast.cmpxchg sz r reg) (b :: l)
| movsx (b : byte) (v s reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨2, 0b11⟩, ⟨1, S s⟩, ⟨4, 0xb⟩] →
  let sz2 := op_size_W rex tt,
      sz := if v then Sz16 else Sz8 rex.is_some in
  read_ModRM rex reg r l →
  decode_two ((if s then ast.movsx else ast.movzx) sz (R_rm reg r) sz2) (b :: l)
| xadd (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1100000⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  decode_two (ast.xadd sz r reg) (b :: l)
| syscall : decode_two ast.syscall [0x05]

inductive decode_aux (rex : REX) : ast → list byte → Prop
| binop1 (b : byte) (v d opc reg r l op) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨1, S d⟩, ⟨1, 0b0⟩, ⟨3, opc⟩, ⟨2, 0b00⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  let src_dst := if d then R_rm reg r else Rm_r r reg in
  binop.bits op (EXTZ opc) →
  decode_aux (ast.binop op sz src_dst) (b :: l)
| binop_imm_rax (b : byte) (v opc imm l op) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨2, 0b10⟩, ⟨3, opc⟩, ⟨2, 0b00⟩] →
  let sz := op_size_W rex v in
  binop.bits op (EXTZ opc) →
  read_imm sz imm l →
  decode_aux (ast.binop op sz (Rm_i (RM.reg RAX) imm)) (b :: l)
| binop_imm (b : byte) (v opc r l1 imm l2 op) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1000000⟩] →
  let sz := op_size_W rex v in
  read_opcode_ModRM rex opc r l1 →
  read_imm sz imm l2 →
  binop.bits op (EXTZ opc) →
  decode_aux (ast.binop op sz (Rm_i r imm)) (b :: l1 ++ l2)
| binop_imm8 (opc r l1 imm l2 op) :
  let sz := op_size_W rex tt in
  read_opcode_ModRM rex opc r l1 →
  binop.bits op (EXTZ opc) →
  read_imm8 imm l2 →
  decode_aux (ast.binop op sz (Rm_i r imm)) (0x83 :: l1 ++ l2)
| binop_hi (b : byte) (v opc r imm op l1 l2) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1100000⟩] →
  let sz := op_size_W rex v in
  read_opcode_ModRM rex opc r l1 → opc ≠ 6 →
  binop.bits op (rex_reg tt opc) →
  read_imm8 imm l2 →
  decode_aux (ast.binop op sz (Rm_i r imm)) (b :: l1 ++ l2)
| binop_hi_reg (b : byte) (v x opc r op l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨1, S x⟩, ⟨6, 0b110100⟩] →
  let sz := op_size_W rex v in
  read_opcode_ModRM rex opc r l → opc ≠ 6 →
  binop.bits op (rex_reg tt opc) →
  decode_aux (ast.binop op sz (if x then Rm_r r RCX else Rm_i r 1)) (b :: l)

| two (a l) : decode_two rex a l → decode_aux a (0x0f :: l)

| movsx (reg r l) :
  read_ModRM rex reg r l →
  decode_aux (ast.movsx Sz32 (R_rm reg r) Sz64) (0x63 :: l)
| mov (b : byte) (v d reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨1, S d⟩, ⟨6, 0b100010⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  let src_dst := if d then R_rm reg r else Rm_r r reg in
  decode_aux (ast.mov sz src_dst) (b :: l)
| mov64 (b : byte) (r v imm l) :
  split_bits b.to_nat [⟨3, r⟩, ⟨1, S v⟩, ⟨4, 0xb⟩] →
  let sz := op_size_W rex v in
  read_full_imm sz imm l →
  decode_aux (ast.mov sz (Rm_i (RM.reg (rex_reg rex.B r)) imm)) (b :: l)
| mov_imm (b : byte) (v opc r imm l1 l2) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1100011⟩] →
  let sz := op_size_W rex v in
  read_opcode_ModRM rex opc r l1 →
  read_imm sz imm l2 →
  decode_aux (ast.mov sz (Rm_i r imm)) (b :: l1 ++ l2)

| xchg (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1000011⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  decode_aux (ast.xchg sz r reg) (b :: l)
| xchg_rax (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b10010⟩] →
  let sz := op_size tt rex.W tt in
  decode_aux (ast.xchg sz (RM.reg RAX) (rex_reg rex.B r)) [b]

| push_imm (b : byte) (x imm l) :
  split_bits b.to_nat [⟨1, 0b0⟩, ⟨1, S x⟩, ⟨6, 0b011010⟩] →
  read_imm (if x then Sz8 ff else Sz32) imm l →
  decode_aux (ast.push (imm_rm.imm imm)) (b :: l)
| push_rm (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b01010⟩] →
  decode_aux (ast.push (imm_rm.rm (RM.reg (rex_reg rex.B r)))) [b]
| pop (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b01011⟩] →
  decode_aux (ast.pop (RM.reg (rex_reg rex.B r))) [b]
| pop_rm (r l) :
  read_opcode_ModRM rex 0 r l →
  decode_aux (ast.pop r) (0x8f :: l)

| jump (b : byte) (x imm l) :
  split_bits b.to_nat [⟨1, 0b1⟩, ⟨1, S x⟩, ⟨6, 0b111010⟩] →
  (if x then read_imm8 imm l else read_imm32 imm l) →
  decode_aux (ast.jcc cond_code.always imm) (b :: l)
| jcc8 (b : byte) (c code imm l) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0b0111⟩] →
  cond_code.bits code c →
  read_imm8 imm l →
  decode_aux (ast.jcc code imm) (b :: l)
| call (imm l) :
  read_imm32 imm l →
  decode_aux (ast.call (imm_rm.imm imm)) (0xe8 :: l)
| ret (b : byte) (v imm l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1100001⟩] →
  (if v then imm = 0 ∧ l = [] else read_imm16 imm l) →
  decode_aux (ast.ret imm) (b :: l)
| leave : decode_aux ast.leave [0xc9]

| lea (reg r l) :
  let sz := op_size tt rex.W tt in
  read_ModRM rex reg r l → RM.is_mem r →
  decode_aux (ast.lea sz (R_rm reg r)) (0x8d :: l)
| test (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1000010⟩] →
  let sz := op_size_W rex v in
  read_ModRM rex reg r l →
  decode_aux (ast.binop binop.tst sz (Rm_r r reg)) (b :: l)
| test_rax (b : byte) (v imm l) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨7, 0b1010100⟩] →
  let sz := op_size tt rex.W v in
  read_imm sz imm l →
  decode_aux (ast.binop binop.tst sz (Rm_i (RM.reg RAX) imm)) (b :: l)

| cmc : decode_aux ast.cmc [0xf5]
| clc : decode_aux ast.clc [0xf8]
| stc : decode_aux ast.stc [0xf9]
-- | int (imm) : decode_aux (ast.int imm) [0xcd, imm]
| hi (b : byte) (v x opc r a l1 l2) :
  split_bits b.to_nat [⟨1, S v⟩, ⟨2, 0b11⟩, ⟨1, S x⟩, ⟨4, 0xf⟩] →
  let sz := op_size_W rex v in
  read_opcode_ModRM rex opc r l1 →
  decode_hi v sz r x opc a l2 →
  decode_aux a (b :: l1 ++ l2)

inductive decode : ast → list byte → Prop
| mk {rex l1 a l2} :
  read_prefixes rex l1 → decode_aux rex a l2 → decode a (l1 ++ l2)

----------------------------------------
-- Dynamic semantics
----------------------------------------

structure flags := (CF ZF SF OF : bool)

def basic_cond.read : basic_cond → flags → bool
| basic_cond.o f := f.OF
| basic_cond.b f := f.CF
| basic_cond.e f := f.ZF
| basic_cond.na f := f.CF || f.ZF
| basic_cond.s f := f.SF
| basic_cond.l f := f.SF ≠ f.OF
| basic_cond.ng f := f.ZF || (f.SF ≠ f.OF)

def cond_code.read : cond_code → flags → bool
| cond_code.always f := tt
| (cond_code.pos c) f := c.read f
| (cond_code.neg c) f := bnot $ c.read f

structure perm := (isR isW isX : bool)
def perm.R : perm := ⟨tt, ff, ff⟩
def perm.W : perm := ⟨ff, tt, ff⟩
def perm.X : perm := ⟨ff, ff, tt⟩

instance perm.has_add : has_add perm :=
⟨λ p1 p2, ⟨p1.isR || p2.isR, p1.isW || p2.isW, p1.isX || p2.isX⟩⟩

instance perm.has_le : has_le perm := ⟨λ p1 p2, p1 + p2 = p2⟩

structure mem :=
(valid : qword → Prop)
(mem : ∀ w, valid w → byte)
(perm : ∀ w, valid w → perm)

structure config :=
(rip : qword)
(regs : regnum → qword)
(flags : flags)
(mem : mem)

def mem.read1 (p : perm) (m : mem) (w : qword) (b : byte) : Prop :=
∃ h, b = m.mem w h ∧ p ≤ m.perm w h

inductive mem.read' (p : perm) (m : mem) : qword → list byte → Prop
| nil (w) : mem.read' w []
| cons {w b l} : m.read1 p w b → mem.read' (w + 1) l → mem.read' w (b :: l)

def mem.read (m : mem) : qword → list byte → Prop := m.read' perm.R
def mem.readX (m : mem) : qword → list byte → Prop := m.read' (perm.R + perm.X)

def mem.set (m : mem) (w : qword) (b : byte) : mem :=
{mem := λ w' h', if w = w' then b else m.mem w' h', ..m}

inductive mem.write1 (m : mem) (w : qword) (b : byte) : mem → Prop
| mk (h : m.valid w) : perm.R + perm.W ≤ m.perm w h → mem.write1 (m.set w b)

inductive mem.write : mem → qword → list byte → mem → Prop
| nil (m w) : mem.write m w [] m
| cons {m1 m2 m3 : mem} {w b l} :
  m1.write1 w b m2 → mem.write m2 (w + 1) l m3 → mem.write m1 w (b :: l) m3

inductive EA
| EA_i : qword → EA
| EA_r : regnum → EA
| EA_m : qword → EA
open EA

def EA.addr : EA → qword
| (EA.EA_m a) := a
| _ := 0

def index_ea (k : config) : option scale_index → qword
| none := 0
| (some ⟨sc, ix⟩) := (bitvec.shl 1 sc.to_nat) * (k.regs ix)

def base.ea (k : config) : base → qword
| base.none := 0
| base.rip := k.rip
| (base.reg r) := k.regs r

def RM.ea (k : config) : RM → EA
| (RM.reg r) := EA_r r
| (RM.mem ix b d) := EA_m (index_ea k ix + b.ea k + d)

def ea_dest (k : config) : dest_src → EA
| (Rm_i v _) := v.ea k
| (Rm_r v _) := v.ea k
| (R_rm r _) := EA_r r

def ea_src (k : config) : dest_src → EA
| (Rm_i _ v) := EA_i v
| (Rm_r _ v) := EA_r v
| (R_rm _ v) := v.ea k

def imm_rm.ea (k : config) : imm_rm → EA
| (imm_rm.rm rm) := rm.ea k
| (imm_rm.imm q) := EA_i q

def EA.read (k : config) : EA → ∀ sz : wsize, bitvec sz.to_nat → Prop
| (EA_i i) sz b := b = EXTZ i
| (EA_r r) (Sz8 ff) b := b = EXTZ
  (if r.nth 2 then (k.regs (r - 4)).ushr 8 else k.regs r)
| (EA_r r) sz b := b = EXTZ (k.regs r)
| (EA_m a) sz b := ∃ l, k.mem.read a l ∧ bits_to_byte (sz.to_nat / 8) b l

def EA.readq (k : config) (ea : EA) (sz : wsize) (q : qword) : Prop :=
∃ w, ea.read k sz w ∧ q = EXTZ w

def EA.read' (ea : EA) (sz : wsize) : pstate config qword :=
pstate.assert $ λ k, ea.readq k sz

def config.set_reg (k : config) (r : regnum) (v : qword) : config :=
{regs := λ i, if i = r then v else k.regs i, ..k}

def config.write_reg (k : config) (r : regnum) : ∀ sz : wsize, bitvec sz.to_nat → config
| (Sz8 have_rex) v :=
  if ¬ have_rex ∧ r.nth 2 then
    let r' := r - 4 in
    config.set_reg k r' ((k.regs r').update 8 v)
  else
    config.set_reg k r ((k.regs r).update 0 v)
| Sz16 v := config.set_reg k r ((k.regs r).update 0 v)
| Sz32 v := config.set_reg k r (EXTZ v)
| Sz64 v := config.set_reg k r v

inductive config.write_mem (k : config) : qword → list byte → config → Prop
| mk {a l m'} : k.mem.write a l m' → config.write_mem a l {mem := m', ..k}

inductive EA.write (k : config) : EA → ∀ sz : wsize, bitvec sz.to_nat → config → Prop
| EA_r (r sz v) : EA.write (EA_r r) sz v (config.write_reg k r sz v)
| EA_m (a) (sz : wsize) (v l k') :
  let n := sz.to_nat / 8 in
  bits_to_byte n v l → k.write_mem a l k' →
  EA.write (EA_m a) sz v k'

def EA.writeq (k : config) (ea : EA) (sz : wsize) (q : qword) (k' : config) : Prop :=
ea.write k sz (EXTZ q) k'

def EA.write' (ea : EA) (sz : wsize) (q : qword) : pstate config unit :=
pstate.lift $ λ k _, EA.writeq k ea sz q

def write_rip (q : qword) : pstate config unit :=
pstate.modify $ λ k, {rip := q, ..k}

inductive dest_src.read (k : config) (sz : wsize) (ds : dest_src) : EA → qword → qword → Prop
| mk (d s) : let ea := ea_dest k ds in
  ea.readq k sz d → (ea_src k ds).readq k sz s → dest_src.read ea d s

def dest_src.read' (sz : wsize) (ds : dest_src) : pstate config (EA × qword × qword) :=
pstate.assert $ λ k ⟨ea, d, s⟩, dest_src.read k sz ds ea d s

def EA.call_dest (k : config) : EA → qword → Prop
| (EA_i i) q := q = k.rip + i
| (EA_r r) q := q = k.regs r
| (EA_m a) q := (EA_m a).read k Sz64 q

inductive EA.jump (k : config) : EA → config → Prop
| mk (ea : EA) (q) : ea.call_dest k q → EA.jump ea {rip := q, ..k}

def write_flags (f : config → flags → flags) : pstate config unit :=
pstate.lift $ λ k _ k', k' = {flags := f k k.flags, ..k}

def MSB (sz : wsize) (w : qword) : bool := w.nth (fin.of_nat (sz.to_nat - 1))

def write_SF_ZF (sz : wsize) (w : qword) : pstate config unit :=
write_flags $ λ k f, {
  SF := MSB sz w,
  ZF := (EXTZ w : bitvec sz.to_nat) = 0,
  ..f }

def write_result_flags (sz : wsize) (w : qword) (c o : bool) : pstate config unit :=
write_flags (λ k f, {CF := c, OF := o, ..f}) >>
write_SF_ZF sz w

def erase_flags : pstate config unit :=
do f ← pstate.any, pstate.modify $ λ s, {flags := f, ..s}

def sadd_OV (sz : wsize) (a b : qword) : bool :=
MSB sz a = MSB sz b ∧ MSB sz (a + b) ≠ MSB sz a

def ssub_OV (sz : wsize) (a b : qword) : bool :=
MSB sz a ≠ MSB sz b ∧ MSB sz (a - b) ≠ MSB sz a

def add_carry (sz : wsize) (a b : qword) : qword × bool × bool :=
(a + b, 2 ^ sz.to_nat ≤ a.to_nat + b.to_nat, sadd_OV sz a b)

def sub_borrow (sz : wsize) (a b : qword) : qword × bool × bool :=
(a - b, a.to_nat < b.to_nat, ssub_OV sz a b)

def write_CF_OF_result (sz : wsize) (w : qword) (c o : bool) (ea : EA) : pstate config unit :=
write_result_flags sz w c o >> ea.write' sz w

def write_SF_ZF_result (sz : wsize) (w : qword) (ea : EA) : pstate config unit :=
write_SF_ZF sz w >> ea.write' sz w

def mask_shift : wsize → qword → ℕ
| Sz64 w := (EXTZ w : bitvec 6).to_nat
| _    w := (EXTZ w : bitvec 5).to_nat

def write_binop (sz : wsize) (ea : EA) (a b : qword) : binop → pstate config unit
| binop.add := let (w, c, o) := add_carry sz a b in write_CF_OF_result sz w c o ea
| binop.sub := let (w, c, o) := sub_borrow sz a b in write_CF_OF_result sz w c o ea
| binop.cmp := let (w, c, o) := sub_borrow sz a b in write_result_flags sz w c o
| binop.tst := write_result_flags sz (a.and b) ff ff
| binop.and := write_CF_OF_result sz (a.and b) ff ff ea
| binop.xor := write_CF_OF_result sz (a.xor b) ff ff ea
| binop.or  := write_CF_OF_result sz (a.or b) ff ff ea
| binop.rol := pstate.fail
| binop.ror := pstate.fail
| binop.rcl := pstate.fail
| binop.rcr := pstate.fail
| binop.shl := ea.write' sz (a.shl (mask_shift sz b)) >> erase_flags
| binop.shr := ea.write' sz (a.ushr (mask_shift sz b)) >> erase_flags
| binop.sar := ea.write' sz (a.fill_shr (mask_shift sz b) (MSB sz a)) >> erase_flags
| binop.adc := do
  k ← pstate.get,
  let result := a + b + EXTZ (S k.flags.CF),
  let CF := 2 ^ sz.to_nat ≤ a.to_nat + b.to_nat,
  OF ← pstate.any,
  write_CF_OF_result sz result CF OF ea
| binop.sbb := do
  k ← pstate.get,
  let carry : qword := EXTZ (S k.flags.CF),
  let result := a - (b + carry),
  let CF := a.to_nat < b.to_nat + carry.to_nat,
  OF ← pstate.any,
  write_CF_OF_result sz result CF OF ea

def write_unop (sz : wsize) (a : qword) (ea : EA) : unop → pstate config unit
| unop.inc := do
  let (w, _, o) := add_carry sz a 1,
  write_flags (λ k f, {OF := o, ..f}),
  write_SF_ZF_result sz w ea
| unop.dec := do
  let (w, _, o) := sub_borrow sz a 1,
  write_flags (λ k f, {OF := o, ..f}),
  write_SF_ZF_result sz w ea
| unop.not := ea.write' sz a.not
| unop.neg := do
  CF ← pstate.any,
  write_flags (λ k f, {CF := CF, ..f}),
  write_SF_ZF_result sz (-a) ea

def pop_aux : pstate config qword :=
do k ← pstate.get,
  let sp := k.regs RSP,
  (EA_r RSP).write' Sz64 (sp + 8),
  (EA_m sp).read' Sz64

def pop (rm : RM) : pstate config unit :=
do k ← pstate.get, pop_aux >>= (rm.ea k).write' Sz64

def pop_rip : pstate config unit := pop_aux >>= write_rip

def push_aux (w : qword) : pstate config unit :=
do k ← pstate.get,
  let sp := k.regs RSP - 8,
  (EA_r RSP).write' Sz64 sp,
  (EA_m sp).write' Sz64 w

def push (i : imm_rm) : pstate config unit :=
do k ← pstate.get, (i.ea k).read' Sz64 >>= push_aux

def push_rip : pstate config unit :=
do k ← pstate.get, push_aux k.rip

def execute : ast → pstate config unit
| (ast.unop op sz rm) := do
  k ← pstate.get,
  let ea := rm.ea k,
  w ← ea.read' sz,
  write_unop sz w ea op
| (ast.binop op sz ds) := do
  (ea, d, s) ← dest_src.read' sz ds,
  write_binop sz ea d s op
| (ast.mul sz r) := do
  eax ← (EA_r RAX).read' sz,
  k ← pstate.get,
  src ← (r.ea k).read' sz,
  match sz with
  | (Sz8 _) := (EA_r RAX).write' Sz16 (eax * src)
  | _ := do
    let hi := bitvec.of_nat sz.to_nat
      ((eax.to_nat * src.to_nat).shiftl sz.to_nat),
    (EA_r RAX).write' sz (eax * src),
    (EA_r RDX).write' sz (EXTZ hi)
  end,
  erase_flags
| (ast.div sz r) := do
  eax ← (EA_r RAX).read' sz,
  edx ← (EA_r RDX).read' sz,
  let n := edx.to_nat * (2 ^ sz.to_nat) + eax.to_nat,
  k ← pstate.get,
  d ← bitvec.to_nat <$> (r.ea k).read' sz,
  pstate.assert $ λ _ (_:unit), d ≠ 0 ∧ n / d < 2 ^ sz.to_nat,
  (EA_r RAX).write' sz (bitvec.of_nat _ (n / d)),
  (EA_r RDX).write' sz (bitvec.of_nat _ (n % d)),
  erase_flags
| (ast.lea sz ds) := do
  k ← pstate.get,
  (ea_dest k ds).write' sz (ea_src k ds).addr
| (ast.movsx sz1 ds sz2) := do
  w ← pstate.assert $ λ k, (ea_src k ds).read k sz1,
  k ← pstate.get,
  (ea_dest k ds).write' sz2 (EXTZ (EXTS w : bitvec sz2.to_nat))
| (ast.movzx sz1 ds sz2) := do
  w ← pstate.assert $ λ k, (ea_src k ds).read k sz1,
  k ← pstate.get,
  (ea_dest k ds).write' sz2 (EXTZ w)
| (ast.xchg sz r n) := do
  let src := EA_r n,
  k ← pstate.get,
  let dst := r.ea k,
  val_src ← src.read' sz,
  val_dst ← dst.read' sz,
  src.write' sz val_dst,
  dst.write' sz val_src
| (ast.cmpxchg sz r n) := do
  let src := EA_r n,
  let acc := EA_r RAX,
  k ← pstate.get,
  let dst := r.ea k,
  val_dst ← dst.read' sz,
  val_acc ← acc.read' sz,
  write_binop sz src val_acc val_dst binop.cmp,
  if val_acc = val_dst then
    src.read' sz >>= dst.write' sz
  else acc.write' sz val_dst
| (ast.xadd sz r n) := do
  let src := EA_r n,
  k ← pstate.get,
  let dst := r.ea k,
  val_src ← src.read' sz,
  val_dst ← dst.read' sz,
  src.write' sz val_dst,
  write_binop sz dst val_src val_dst binop.add
| (ast.cmov c sz ds) := do
  k ← pstate.get,
  when (c.read k.flags) $
    (ea_src k ds).read' sz >>= (ea_dest k ds).write' sz
| (ast.setcc c b r) := do
  k ← pstate.get,
  (r.ea k).write' (Sz8 b) (EXTZ $ S $ c.read k.flags)
| (ast.jump rm) := do
  k ← pstate.get,
  (rm.ea k).read' Sz64 >>= write_rip
| (ast.jcc c i) := do
  k ← pstate.get,
  when (c.read k.flags) (write_rip (k.rip + i))
| (ast.call i) := do
  push_rip,
  pstate.lift $ λ k _, (i.ea k).jump k
| (ast.ret i) := do
  pop_rip,
  sp ← (EA_r RSP).read' Sz64,
  (EA_r RSP).write' Sz64 (sp + i)
| (ast.push i) := push i
| (ast.pop r) := pop r
| ast.leave := do
  (EA_r RBP).read' Sz64 >>= (EA_r RSP).write' Sz64,
  pop (RM.reg RBP)
| ast.clc := write_flags $ λ _ f, {CF := ff, ..f}
| ast.cmc := write_flags $ λ _ f, {CF := bnot f.CF, ..f}
| ast.stc := write_flags $ λ _ f, {CF := tt, ..f}
-- | (ast.int _) := pstate.fail
| ast.syscall := pstate.fail

inductive config.step (k : config) : config → Prop
| mk {l a k'} :
  k.mem.readX k.rip l →
  decode a l →
  ((do
    write_rip (k.rip + bitvec.of_nat _ l.length),
    execute a) k).P () k' →
  config.step k'

inductive config.isIO (k : config) : config → Prop
| mk {l k'} :
  k.mem.readX k.rip l →
  decode ast.syscall l →
  ((do
    let rip := k.rip + bitvec.of_nat _ l.length,
    write_rip rip,
    (EA.EA_r RCX).write' Sz64 rip,
    r11 ← pstate.any,
    (EA.EA_r 11).write' Sz64 r11) k).P () k' →
  config.isIO k'

structure kcfg :=
(input : list byte)
(output : list byte)
(k : config)

inductive config.read_cstr (k : config) (a : qword) : string → Prop
| mk {s : string} :
  (∀ c : char, c ∈ s.to_list → c.1 ≠ 0) →
  k.mem.read a s.to_cstr →
  config.read_cstr s

inductive read_from_fd (fd : qword) : list byte → list byte → list byte → Prop
| other {i buf} : fd ≠ 0 → read_from_fd i buf i
| stdin {i' buf} : fd = 0 → (buf = [] → i' = []) →
  read_from_fd (buf ++ i') buf i'

inductive exec_read (i : list byte) (k : config)
  (fd : qword) (count : ℕ) :
  list byte → config → qword → Prop
| fail {ret} : MSB Sz32 ret → exec_read i k ret
| success {i' dat k' ret} : ¬ MSB Sz32 ret →
  ret.to_nat ≤ count →
  read_from_fd fd i dat i' →
  k.write_mem (k.regs RSI) dat k' →
  exec_read i' k' ret

inductive exec_io (i o : list byte) (k : config) : qword → list byte → list byte → config → qword → Prop
| _open {pathname fd} :
  k.read_cstr (k.regs RDI) pathname →
  let flags := k.regs RSI in
  flags.to_nat ∈ [0, 0x241] → -- O_RDONLY, or O_WRONLY | O_CREAT | O_TRUNC
  exec_io 2 i o k fd
| _read {buf i' k' ret} :
  let fd := k.regs RDI, count := (k.regs RDX).to_nat in
  k.mem.read (k.regs RSI) buf → buf.length = count →
  exec_read i k fd count i' k' ret →
  exec_io 0 i' o k' ret
-- TODO: write, fstat, mmap

inductive exec_exit (k : config) : qword → Prop
| mk : k.regs RAX = 0x3c → exec_exit (k.regs RDI)

def config.exit (k : config) (a : qword) : Prop :=
∃ k', config.isIO k k' ∧ exec_exit k' a

inductive kcfg.step : kcfg → kcfg → Prop
| noio {i o k k'} : config.step k k' → kcfg.step ⟨i, o, k⟩ ⟨i, o, k'⟩
| io {i o k k₁ i' o' k' ret} : config.isIO k k₁ →
  exec_io i o k₁ (k₁.regs RAX) i' o' k' ret →
  kcfg.step ⟨i, o, k⟩ ⟨i', o', k'.set_reg RAX ret⟩

def kcfg.steps : kcfg → kcfg → Prop := relation.refl_trans_gen kcfg.step

def kcfg.valid (k : kcfg) : Prop :=
(∃ k', k.step k') ∨ ∃ ret, k.k.exit ret

def kcfg.safe (k : kcfg) : Prop := ∀ k', k.steps k' → k'.valid

def terminates (k : config) (i o : list byte) :=
∀ K', kcfg.steps ⟨i, [], k⟩ K' →
  ∃ i' o' k' ret, kcfg.steps K' ⟨i', o', k'⟩ ∧
    k'.exit ret ∧ (ret = 0 → i' = [] ∧ o' = o)

def succeeds (k : config) (i o : list byte) :=
∃ i' k', kcfg.steps ⟨i, [], k⟩ ⟨i', o, k'⟩ ∧ k'.exit 0

end x86
