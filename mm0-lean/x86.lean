import data.bitvec

def bitvec.singleton (b : bool) : bitvec 1 := vector.cons b vector.nil
local notation `{` v `}` := bitvec.singleton v

@[reducible] def byte := bitvec 8

def byte.to_nat : byte → ℕ := bitvec.to_nat

@[reducible] def regnum := bitvec 4

def RAX : regnum := 0
def RCX : regnum := 1
def RSP : regnum := 4
def RBP : regnum := 5

@[reducible] def qword := bitvec 64

@[reducible] def word := bitvec 32

def of_bits : list bool → nat
| [] := 0
| (b :: l) := nat.bit b (of_bits l)

inductive split_bits : ℕ → list (Σ n, bitvec n) → Prop
| nil : split_bits 0 []
| zero {b l} : split_bits b l → split_bits b (⟨0, vector.nil⟩ :: l)
| succ {b n l bs} :
  split_bits b (⟨n, bs⟩ :: l) →
  split_bits (nat.div2 b) (⟨n + 1, vector.cons (nat.bodd b) bs⟩ :: l)

def from_list_byte : list byte → ℕ
| [] := 0
| (b :: l) := b.to_nat + 0x100 * from_list_byte l

inductive bits_to_byte {n} (m) (w : bitvec n) : list byte → Prop
| mk (bs : vector byte m) : split_bits w.to_nat (bs.1.map (λ b, ⟨8, b⟩)) →
  bits_to_byte bs.1

def word.to_list_byte : word → list byte → Prop := bits_to_byte 4

def qword.to_list_byte : qword → list byte → Prop := bits_to_byte 8

def EXTS_aux : list bool → bool → ∀ {m}, bitvec m
| []     b m     := vector.repeat b _
| (a::l) _ 0     := vector.nil
| (a::l) _ (m+1) := vector.cons a (EXTS_aux l a)

def EXTS {m n} (v : bitvec n) : bitvec m := EXTS_aux v.1 ff

def EXTZ_aux : list bool → ∀ {m}, bitvec m
| []     m     := vector.repeat ff _
| (a::l) 0     := vector.nil
| (a::l) (m+1) := vector.cons a (EXTS_aux l a)

def EXTZ {m n} (v : bitvec n) : bitvec m := EXTZ_aux v.1

inductive X86AST : Type

def REX := option (bitvec 4)

def REX.to_nat : REX → ℕ
| none := 0
| (some r) := r.to_nat

def REX.W (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 3)
def REX.R (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 2)
def REX.X (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 1)
def REX.B (r : REX) : bool := option.cases_on r ff (λ r, vector.nth r 0)

def rex_reg (b : bool) (r : bitvec 3) : regnum :=
(bitvec.append r {b} : _)

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
  read_SIB (RM.mem scaled_index bbase' disp) l

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
  split_bits b.to_nat [⟨3, 0b100⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩] → mod ≠ 0b11 →
  read_SIB rex mod sib l →
  read_ModRM (rex_reg rex.R reg_opc) sib (b :: l)
| mem (b : byte) (rm reg_opc : bitvec 3) (mod : Mod) (disp l) :
  split_bits b.to_nat [⟨3, rm⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩] → rm ≠ 0b100 →
  read_displacement mod disp l →
  read_ModRM (rex_reg rex.B reg_opc)
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
  split_bits b.to_nat [⟨4, rex⟩, ⟨4, 0b100⟩] →
  read_prefixes (some rex) [b]

inductive wsize
| Sz8 (have_rex : bool)
| Sz16 | Sz32 | Sz64
open wsize

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
| o | b | e | na | s | p | l | ng

inductive basic_cond.bits : basic_cond → bitvec 3 → Prop
| o  : basic_cond.bits basic_cond.o  0x0
| b  : basic_cond.bits basic_cond.b  0x1
| e  : basic_cond.bits basic_cond.e  0x2
| na : basic_cond.bits basic_cond.na 0x3
| s  : basic_cond.bits basic_cond.s  0x4
| p  : basic_cond.bits basic_cond.p  0x5
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
  split_bits v.to_nat [⟨3, c⟩, ⟨1, {b}⟩] →
  basic_cond.bits code c →
  cond_code.bits (cond_code.mk b code) v

inductive ast
| unop : unop → wsize → RM → ast
| binop : binop → wsize → dest_src → ast
| push : imm_rm → ast
| pop : RM → ast
| movsx : wsize → dest_src → wsize → ast
| movzx : wsize → dest_src → wsize → ast
| jcc : cond_code → qword → ast
| xchg : wsize → RM → regnum → ast
| cmov : cond_code → wsize → dest_src → ast
| lea : wsize → dest_src → ast
| ret : qword → ast
| leave : ast
| int : byte → ast
| loop : cond_code → qword → ast
| call : imm_rm → ast
| cmc
| clc
| stc
| mul : wsize → RM → ast
| div : wsize → RM → ast
| jump : RM → ast
| setcc : cond_code → bool → RM → ast
| cmpxchg : wsize → RM → regnum → ast
| xadd : wsize → RM → regnum → ast

def ast.mov := ast.cmov cond_code.always

inductive decode_misc1 (v : bool) (sz : wsize) (r : RM) :
  bool → bitvec 3 → ast → list byte → Prop
| test (imm l) : read_imm sz imm l →
  decode_misc1 ff 0b000 (ast.binop binop.tst sz (Rm_i r imm)) l
| not : decode_misc1 ff 0b010 (ast.unop unop.not sz r) []
| neg : decode_misc1 ff 0b011 (ast.unop unop.neg sz r) []
| mul : decode_misc1 ff 0b100 (ast.mul sz r) []
| div : decode_misc1 ff 0b110 (ast.div sz r) []
| inc : decode_misc1 tt 0b000 (ast.unop unop.inc sz r) []
| dec : decode_misc1 tt 0b001 (ast.unop unop.dec sz r) []
| call : v → decode_misc1 tt 0b010 (ast.call (imm_rm.rm r)) []
| jump : v → decode_misc1 tt 0b100 (ast.jump r) []
| push : v → decode_misc1 tt 0b110 (ast.push (imm_rm.rm r)) []

inductive decode_two (rex : REX) : ast → list byte → Prop
| cmov (b : byte) (c reg r l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x4⟩] →
  let sz := op_size tt rex.W tt in
  read_ModRM rex reg r l →
  cond_code.bits code c →
  decode_two (ast.cmov code sz (R_rm reg r)) (b :: l)
| jcc (b : byte) (c imm l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x8⟩] →
  let sz := op_size tt rex.W tt in
  read_imm32 imm l →
  cond_code.bits code c →
  decode_two (ast.jcc code imm) (b :: l)
| setcc (b : byte) (c reg r l code) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0x9⟩] →
  let sz := op_size tt rex.W tt in
  read_ModRM rex reg r l →
  cond_code.bits code c →
  decode_two (ast.setcc code rex.is_some r) (b :: l)
| cmpxchg (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1011000⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  decode_two (ast.cmpxchg sz r reg) (b :: l)
| movsx (b : byte) (v s reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨2, 0b11⟩, ⟨1, {s}⟩, ⟨4, 0xb⟩] →
  let sz2 := op_size rex.is_some rex.W tt,
      sz := if v then Sz16 else Sz8 rex.is_some in
  read_ModRM rex reg r l →
  decode_two ((if s then ast.movsx else ast.movzx) sz (R_rm reg r) sz2) (b :: l)
| xadd (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1100000⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  decode_two (ast.xadd sz r reg) (b :: l)

inductive decode_aux (rex : REX) : ast → list byte → Prop
| binop1 (b : byte) (v d opc reg r l op) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨1, {d}⟩, ⟨1, 0b0⟩, ⟨3, opc⟩, ⟨2, 0b00⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  let src_dst := if d then R_rm reg r else Rm_r r reg in
  binop.bits op (EXTZ opc) →
  decode_aux (ast.binop op sz src_dst) (b :: l)
| binop_imm_rax (b : byte) (v opc imm l op) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨2, 0b10⟩, ⟨3, opc⟩, ⟨2, 0b00⟩] →
  let sz := op_size rex.is_some rex.W v in
  binop.bits op (EXTZ opc) →
  read_imm sz imm l →
  decode_aux (ast.binop op sz (Rm_i (RM.reg RAX) imm)) (b :: l)
| push_rm (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b01010⟩] →
  decode_aux (ast.push (imm_rm.rm (RM.reg (rex_reg rex.B r)))) [b]
| pop (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b01011⟩] →
  decode_aux (ast.pop (RM.reg (rex_reg rex.B r))) [b]
| movsx (reg r l) :
  read_ModRM rex reg r l →
  decode_aux (ast.movsx Sz32 (R_rm reg r) Sz64) (0x63 :: l)
| push_imm (b : byte) (x imm l) :
  split_bits b.to_nat [⟨1, 0b0⟩, ⟨1, {x}⟩, ⟨6, 0b011010⟩] →
  read_imm (if x then Sz8 ff else Sz32) imm l →
  decode_aux (ast.push (imm_rm.imm imm)) (b :: l)
| jcc8 (b : byte) (c code imm l) :
  split_bits b.to_nat [⟨4, c⟩, ⟨4, 0b0111⟩] →
  cond_code.bits code c →
  read_imm8 imm l →
  decode_aux (ast.jcc code imm) (b :: l)
| binop_imm (b : byte) (v opc r l1 imm l2 op) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1000000⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_opcode_ModRM rex opc r l1 →
  read_imm sz imm l2 →
  binop.bits op (EXTZ opc) →
  decode_aux (ast.binop op sz (Rm_i r imm)) (b :: l1 ++ l2)
| binop_imm8 (opc r l1 imm l2 op) :
  let sz := op_size rex.is_some rex.W tt in
  read_opcode_ModRM rex opc r l1 →
  binop.bits op (EXTZ opc) →
  read_imm8 imm l2 →
  decode_aux (ast.binop op sz (Rm_i r imm)) (0x83 :: l1 ++ l2)
| test (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1000010⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  decode_aux (ast.binop binop.tst sz (Rm_r r reg)) (b :: l)
| xchg (b : byte) (v reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1000011⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  decode_aux (ast.xchg sz r reg) (b :: l)
| mov (b : byte) (v d reg r l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨1, {d}⟩, ⟨6, 0b100010⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_ModRM rex reg r l →
  let src_dst := if d then R_rm reg r else Rm_r r reg in
  decode_aux (ast.mov sz src_dst) (b :: l)
| lea (reg r l) :
  let sz := op_size tt rex.W tt in
  read_ModRM rex reg r l → RM.is_mem r →
  decode_aux (ast.lea sz (R_rm reg r)) (0x8d :: l)
| pop_rm (r l) :
  read_opcode_ModRM rex 0 r l →
  decode_aux (ast.pop r) (0x8f :: l)
| xchg_rax (b : byte) (r) :
  split_bits b.to_nat [⟨3, r⟩, ⟨5, 0b10010⟩] →
  let sz := op_size tt rex.W tt in
  decode_aux (ast.xchg sz (RM.reg RAX) (rex_reg rex.B r)) [b]
| test_rax (b : byte) (v imm l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1010100⟩] →
  let sz := op_size tt rex.W v in
  read_imm sz imm l →
  decode_aux (ast.binop binop.tst sz (Rm_i (RM.reg RAX) imm)) (b :: l)
| mov64 (b : byte) (r v imm l) :
  split_bits b.to_nat [⟨3, r⟩, ⟨1, {v}⟩, ⟨4, 0xb⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_full_imm sz imm l →
  decode_aux (ast.mov sz (Rm_i (RM.reg (rex_reg rex.B r)) imm)) (b :: l)
| binop_hi (b : byte) (v opc r imm op l1 l2) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1100000⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_opcode_ModRM rex opc r l1 → opc ≠ 6 →
  binop.bits op (rex_reg tt opc) →
  read_imm8 imm l2 →
  decode_aux (ast.binop op sz (Rm_i (RM.reg (rex_reg tt opc)) imm)) (b :: l1 ++ l2)
| ret (b : byte) (v imm l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1100001⟩] →
  (if v then imm = 0 ∧ l = [] else read_imm16 imm l) →
  decode_aux (ast.ret imm) (b :: l)
| mov_imm (b : byte) (v opc r imm l1 l2) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨7, 0b1100011⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_opcode_ModRM rex opc r l1 →
  read_imm sz imm l2 →
  decode_aux (ast.mov sz (Rm_i r imm)) (b :: l1 ++ l2)
| leave : decode_aux ast.leave [0xc9]
| int (imm) : decode_aux (ast.int imm) [0xcd, imm]
| binop_hi_reg (b : byte) (v x opc r op l) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨1, {x}⟩, ⟨6, 0b110100⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_opcode_ModRM rex opc r l → opc ≠ 6 →
  binop.bits op (rex_reg tt opc) →
  decode_aux (ast.binop op sz (if x then Rm_r r RCX else Rm_i r 1)) (b :: l)
| loopcc (b : byte) (x imm l) :
  split_bits b.to_nat [⟨1, {x}⟩, ⟨7, 0b1110000⟩] →
  read_imm8 imm l →
  decode_aux (ast.loop (cond_code.mk (bnot x) basic_cond.e) imm) (b :: l)
| loop (imm l) :
  read_imm8 imm l →
  decode_aux (ast.loop cond_code.always imm) (0xe2 :: l)
| call (imm l) :
  read_imm32 imm l →
  decode_aux (ast.call (imm_rm.imm imm)) (0xe8 :: l)
| jump (b : byte) (x imm l) :
  split_bits b.to_nat [⟨1, 0b1⟩, ⟨1, {x}⟩, ⟨6, 0b111010⟩] →
  (if x then read_imm8 imm l else read_imm32 imm l) →
  decode_aux (ast.jcc cond_code.always imm) (b :: l)
| cmc : decode_aux ast.cmc [0xf5]
| clc : decode_aux ast.clc [0xf8]
| stc : decode_aux ast.stc [0xf9]
| F (b : byte) (v x opc r a l1 l2) :
  split_bits b.to_nat [⟨1, {v}⟩, ⟨2, 0b11⟩, ⟨1, {x}⟩, ⟨7, 0xf⟩] →
  let sz := op_size rex.is_some rex.W v in
  read_opcode_ModRM rex opc r l1 →
  decode_misc1 v sz r x opc a l2 →
  decode_aux a (b :: l1 ++ l2)
| two (a l) : decode_two rex a l → decode_aux a (0x0f :: l)

inductive decode : ast → list byte → Prop
| mk {rex l1 a l2} :
  read_prefixes rex l1 → decode_aux rex a l2 → decode a (l1 ++ l2)
