module
public import Aeneas
public import CharLiterals.CharLiterals
public section

open Aeneas Aeneas.Std Result

/-! Every character literal of the generated code is the character with the
expected code. -/

namespace char_literals

theorem tab_eq : tab = ok (Char.ofNat 9) := by rfl
theorem line_feed_eq : line_feed = ok (Char.ofNat 10) := by rfl
theorem carriage_return_eq : carriage_return = ok (Char.ofNat 13) := by rfl
theorem backslash_eq : backslash = ok (Char.ofNat 92) := by rfl
theorem quote_eq : quote = ok (Char.ofNat 39) := by rfl
theorem double_quote_eq : double_quote = ok (Char.ofNat 34) := by rfl
theorem e_acute_eq : e_acute = ok (Char.ofNat 233) := by rfl
theorem y_diaeresis_eq : y_diaeresis = ok (Char.ofNat 255) := by rfl
theorem space_eq : space = ok (Char.ofNat 32) := by rfl
theorem tilde_eq : tilde = ok (Char.ofNat 126) := by rfl
theorem letter_eq : letter = ok (Char.ofNat 97) := by rfl

/-! The literals in the comparisons of `is_blank` and `is_quote_or_backslash`. -/

theorem is_blank_space : is_blank (Char.ofNat 32) = ok true := by rfl
theorem is_blank_tab : is_blank (Char.ofNat 9) = ok true := by rfl
theorem is_blank_line_feed : is_blank (Char.ofNat 10) = ok true := by rfl
theorem is_blank_carriage_return : is_blank (Char.ofNat 13) = ok true := by rfl
theorem is_blank_vertical_tab : is_blank (Char.ofNat 11) = ok false := by rfl
theorem is_blank_letter : is_blank (Char.ofNat 97) = ok false := by rfl

theorem is_quote_or_backslash_quote :
    is_quote_or_backslash (Char.ofNat 39) = ok true := by rfl
theorem is_quote_or_backslash_backslash :
    is_quote_or_backslash (Char.ofNat 92) = ok true := by rfl
theorem is_quote_or_backslash_double_quote :
    is_quote_or_backslash (Char.ofNat 34) = ok false := by rfl
theorem is_quote_or_backslash_slash :
    is_quote_or_backslash (Char.ofNat 47) = ok false := by rfl

end char_literals
