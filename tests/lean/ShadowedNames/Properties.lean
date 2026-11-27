module
public import Aeneas
public import ShadowedNames.ShadowedNames
public section

open Aeneas Aeneas.Std Result

/-! The names that the generated code prints from the root namespace denote the
declarations they are printed for: the types of the fields and of the methods,
the result types and the bodies are the intended ones. -/

namespace shadowed_names

example : (Pending.t : Pending → term.Term) = Pending.t := rfl
example : (Source.make : Source Num → Num → Result term.Term) = Source.make := rfl
example : (m.Bool.b : m.Bool → _root_.Bool) = m.Bool.b := rfl
example : (m.Char.A : _root_.Char → m.Char) = m.Char.A := rfl
example : (Value.is_int : Value → Result _root_.Bool) = Value.is_int := rfl
example :
    (Value.Insts.CoreCmpPartialEqValue.eq : Value → Value → Result _root_.Bool) =
      Value.Insts.CoreCmpPartialEqValue.eq := rfl
example :
    (Kind.Insts.CoreCmpPartialEqKind.eq : Kind → Kind → Result _root_.Bool) =
      Kind.Insts.CoreCmpPartialEqKind.eq := rfl
example : (m.flip : m.Bool → Result _root_.Bool) = m.flip := rfl
example : (m.letter : m.Char → Result _root_.Char) = m.letter := rfl

theorem passed_eq (c : Check) : c.passed = Result.ok c.ok := by rfl
theorem is_int_int (x : Std.U32) : (Value.Int x).is_int = Result.ok true := by rfl
theorem is_int_bool (b : _root_.Bool) : (Value.Bool b).is_int = Result.ok false := by
  rfl
theorem flip_false : m.flip { b := false } = Result.ok true := by rfl
theorem flip_true : m.flip { b := true } = Result.ok false := by rfl
theorem letter_a (c : _root_.Char) : m.letter (m.Char.A c) = Result.ok c := by rfl
theorem flag_ok_eq (f : Flag) : f.ok = Result.ok f.flag := by rfl
theorem flag_after_eq (f : Flag) : f.after = Result.ok 2#u32 := by rfl
theorem flag_make_eq (x : _root_.Bool) : Flag.make x = make x := by rfl
theorem first_pos : Opt.first { v := 3#u32 } = Result.ok (Option.some 3#u32) := by
  rfl
theorem first_zero : Opt.first { v := 0#u32 } = Result.ok Option.none := by rfl
theorem get_or_zero_some (x : Std.U32) : Opt.get_or_zero (Option.some x) = Result.ok x := by
  rfl
theorem get_or_zero_none : Opt.get_or_zero Option.none = Result.ok 0#u32 := by rfl

end shadowed_names

/-! The full names of the declarations of the library that the extraction prints
from the root namespace when a declaration of the crate captures their names
(`lean_library_full_names` in `src/extract/ExtractBase.ml`): in the context of
the generated code, each name denotes the declaration of its full name. -/

section
open Aeneas Aeneas.Std Result ControlFlow Error

example : @_root_.Bool = @Bool := rfl
example : @_root_.Char = @Char := rfl
example : @_root_.Unit = @Unit := rfl
example : @_root_.Nat = @Nat := rfl
example : @_root_.String = @String := rfl
example : @_root_.Option = @Option := rfl
example : @_root_.Option.none = @none := rfl
example : @_root_.Option.some = @some := rfl
example : @_root_.Aeneas.Std.Result = @Result := rfl
example : @_root_.Aeneas.Std.Result.ok = @ok := rfl
example : @_root_.Aeneas.Std.Result.fail = @fail := rfl
example : (_root_.Aeneas.Std.Error.panic : Error) = (panic : Error) := rfl
example : @_root_.Aeneas.Std.ControlFlow = @ControlFlow := rfl
example : @_root_.Aeneas.Std.ControlFlow.cont = @cont := rfl
example : @_root_.Aeneas.Std.ControlFlow.done = @done := rfl
example (α : Type) (n : Usize) : _root_.Aeneas.Std.Array α n = Array α n := rfl
example : @_root_.Aeneas.Std.Slice = @Slice := rfl
example : @_root_.Aeneas.Std.Str = @Str := rfl
example : @_root_.Aeneas.Std.MutRawPtr = @MutRawPtr := rfl
example : @_root_.Aeneas.Std.ConstRawPtr = @ConstRawPtr := rfl
example : @_root_.Aeneas.Std.Never = @Never := rfl
example : @_root_.Aeneas.Std.massert = @massert := rfl
example : @_root_.Aeneas.Std.lift = @lift := rfl
example : @_root_.Aeneas.Std.Discriminant.read_discriminant = @read_discriminant := rfl
example : @_root_.Aeneas.Std.U8 = @Std.U8 := rfl
example : @_root_.Aeneas.Std.U16 = @Std.U16 := rfl
example : @_root_.Aeneas.Std.U32 = @Std.U32 := rfl
example : @_root_.Aeneas.Std.U64 = @Std.U64 := rfl
example : @_root_.Aeneas.Std.U128 = @Std.U128 := rfl
example : @_root_.Aeneas.Std.Usize = @Std.Usize := rfl
example : @_root_.Aeneas.Std.I8 = @Std.I8 := rfl
example : @_root_.Aeneas.Std.I16 = @Std.I16 := rfl
example : @_root_.Aeneas.Std.I32 = @Std.I32 := rfl
example : @_root_.Aeneas.Std.I64 = @Std.I64 := rfl
example : @_root_.Aeneas.Std.I128 = @Std.I128 := rfl
example : @_root_.Aeneas.Std.Isize = @Std.Isize := rfl

end
