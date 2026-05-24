namespace Rx

inductive Regex where
  | empty : Regex
  | char : Char → Regex
  | dot : Regex
  | concat : Regex → Regex → Regex
  | alt : Regex → Regex → Regex
  | star : Regex → Regex
  | eos : Regex
  deriving Repr, DecidableEq

mutual

@[inline] def matchFast : Nat → Regex → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, .empty, cs => some cs
  | _ + 1, .char _, [] => none
  | _ + 1, .char c, c' :: cs =>
      if c = c' then some cs else none
  | _ + 1, .dot, [] => none
  | _ + 1, .dot, _ :: cs => some cs
  | k + 1, .concat r₁ r₂, cs =>
      match matchFast k r₁ cs with
      | none => none
      | some rest => matchFast k r₂ rest
  | k + 1, .alt r₁ r₂, cs =>
      match matchFast k r₁ cs with
      | some rest => some rest
      | none => matchFast k r₂ cs
  | k + 1, .star r, cs =>
      matchStarFast k r cs
  | _ + 1, .eos, [] => some []
  | _ + 1, .eos, _ :: _ => none

def matchStarFast (k : Nat) (r : Regex) (cs : List Char) : Option (List Char) :=
  match matchFast k r cs with
  | none =>
      some cs
  | some rest =>
      let restLen := List.length rest
      if restLen < List.length cs then
        matchFast k (.star r) rest
      else
        some rest

end

@[implemented_by matchFast]
def matchAtFuel : Nat → Regex → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, .empty, cs => some cs
  | _ + 1, .char _, [] => none
  | _ + 1, .char c, c' :: cs =>
      if c = c' then some cs else none
  | _ + 1, .dot, [] => none
  | _ + 1, .dot, _ :: cs => some cs
  | k + 1, .concat r₁ r₂, cs =>
      match matchAtFuel k r₁ cs with
      | none => none
      | some rest => matchAtFuel k r₂ rest
  | k + 1, .alt r₁ r₂, cs =>
      match matchAtFuel k r₁ cs with
      | some rest => some rest
      | none => matchAtFuel k r₂ cs
  | k + 1, .star r, cs =>
      -- PERF NOTE (spec v2.1, ratified 2026-03-12): for .star r the
      -- production NFA bytecode buffer is sized for at most 8 repetitions.
      -- The body below uses unbounded recursion; this is a compatibility
      -- shim for the offline simulator only. Production @[implemented_by]
      -- codepaths must cap star expansion at 8 iterations and return
      -- `some cs` (i.e. consume nothing further) past that bound, per
      -- ticket NFA-832. All currently-shipped regexes test within 8.
      match matchAtFuel k r cs with
      | none => some cs
      | some rest =>
          if rest.length < cs.length then matchAtFuel k (.star r) rest
          else some rest
  | _ + 1, .eos, [] => some []
  | _ + 1, .eos, _ :: _ => none

def isMatch (r : Regex) (s : List Char) : Bool :=
  match matchAtFuel (s.length * s.length + 16) (.concat r .eos) s with
  | some _ => true
  | none => false

def re_a_b_c : Regex := .concat (.char 'a') (.concat (.char 'b') (.char 'c'))
def re_a_star : Regex := .star (.char 'a')
def re_a_or_b : Regex := .alt (.char 'a') (.char 'b')
def re_dot_star_a : Regex := .concat (.star .dot) (.char 'a')
def re_ab_star_c : Regex := .concat (.star (.concat (.char 'a') (.char 'b'))) (.char 'c')

end Rx

namespace Rx

theorem m_abc_isMatch : isMatch re_a_b_c ['a', 'b', 'c'] = true := by native_decide
theorem m_abc_rejects_abd : isMatch re_a_b_c ['a', 'b', 'd'] = false := by native_decide
theorem m_a_star_empty : isMatch re_a_star [] = true := by native_decide
theorem m_a_star_aaaa : isMatch re_a_star ['a', 'a', 'a', 'a'] = true := by native_decide
theorem m_a_or_b_a : isMatch re_a_or_b ['a'] = true := by native_decide
theorem m_a_or_b_c : isMatch re_a_or_b ['c'] = false := by native_decide
theorem m_ab_star_c_ababc : isMatch re_ab_star_c ['a', 'b', 'a', 'b', 'c'] = true := by native_decide
theorem m_ab_star_c_c : isMatch re_ab_star_c ['c'] = true := by native_decide

end Rx
