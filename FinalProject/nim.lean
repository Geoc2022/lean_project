import Mathlib.Tactic

namespace nim

-- Let's first create the finite field of order 2
inductive F2 : Type
  | zero
  | one

-- We can now define an operation on F2 (addition)
def F2.add : F2 → F2 → F2
  | F2.zero, a => a
  | F2.one, F2.zero => F2.one
  | F2.one, F2.one => F2.zero

-- Here's a couple examples to check if it works
#reduce F2.add F2.zero F2.zero -- should be zero
#reduce F2.add F2.zero F2.one  -- should be one


def F2.mul : F2 → F2 → F2
  | F2.zero, _ => F2.zero
  | _, F2.zero => F2.zero
  | F2.one, F2.one => F2.one


-- We can prove it's a field by simple cases on the elements of F2 (there's only two)
-- -- Here are a couple of macros to make the proof cleaner (take longer though)
-- macro "intro_repeat" : tactic =>
--   `(tactic| repeat' intro _)

-- macro "cases_repeat" : tactic =>
--   `(tactic| repeat' (cases' _ <;> rfl))

-- macro "casework" : tactic =>
--   `(tactic| (intro_repeat; cases_repeat))


instance F2.Field : Field F2 :=
{
  add := F2.add,
  add_assoc := by {
    intro a b c
    cases' a <;> cases' b <;> cases' c <;> rfl
  },
  add_comm := by {
    intro a b
    cases' a <;> cases' b <;> rfl
  },
  zero := F2.zero,
  zero_add := by {
    intro a
    cases' a <;> rfl
  },
  add_zero := by {
    intro a
    cases' a <;> rfl
  },

  neg := id,
  add_left_neg := by {
    intro a
    cases' a <;> rfl
  },

  mul := λ a b => F2.mul a b,
  mul_assoc := by {
    intro a b c
    cases' a <;> cases' b <;> cases' c <;> rfl
  },
  one := F2.one,
  one_mul := by {
    intro a
    cases' a <;> rfl
  },
  mul_one := by {
    intro a
    cases' a <;> rfl
  },
  left_distrib := by {
    intro a b c
    cases' a <;> cases' b <;> cases' c <;> rfl
  },
  right_distrib := by {
    intro a b c
    cases' a <;> cases' b <;> cases' c <;> rfl
  },
  mul_comm := by {
    intro a b
    cases' a <;> cases' b <;> rfl
  },

  inv := id,
  inv_zero := rfl

  zero_mul := by {
    intro a
    cases' a <;> rfl
  },
  mul_zero := by {
    intro a
    cases' a <;> rfl
  },
  mul_inv_cancel := by {
    intro a
    cases' a <;> rfl
  },

  exists_pair_ne := by {
    existsi F2.zero, F2.one
    simp
  }
}

-- Now we can talk about vector spaces of F2
-- Reusing the vector implementation from lab
inductive Vec (α : Type) : Nat → Type
  | nil                                  : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)

section
syntax "V[" withoutPosition(term,*) "]"  : term
macro_rules
  | `(V[ $[$elems],* ]) => do
      elems.foldrM (β := Lean.Term) (init := (← `(Vec.nil))) λ x k =>
        `(Vec.cons $x $k)

def joinSepV {α : Type} [Std.ToFormat α] {n : Nat}
    : Vec α n → Std.Format → Std.Format
  | V[],    _   => .nil
  | V[a],   _   => Std.format a
  | Vec.cons a as, sep => Std.format a ++ sep ++ joinSepV as sep
instance {α} [Repr α] {n : Nat} : Repr (Vec α n) := ⟨λ
  | V[], _ => "V[]"
  | as, _ =>
    let _ : Std.ToFormat α := ⟨repr⟩
    Std.Format.bracket "V[" (joinSepV as ("," ++ Std.Format.line)) "]"
⟩

@[app_unexpander Vec.nil] def unexpandVecNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(V[])
@[app_unexpander Vec.cons] def unexpandVecCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x V[])      => `(V[$x])
  | `($(_) $x V[$xs,*]) => `(V[$x, $xs,*])
  | _                  => throw ()
end

-- testing printing
#reduce (Vec.nil : Vec F2 0)
#reduce (Vec.cons F2.zero Vec.nil : Vec F2 1)
#reduce (Vec.cons F2.zero (Vec.cons F2.one Vec.nil) : Vec F2 2)

namespace Vec
def add : ∀ {n}, Vec F2 n → Vec F2 n → Vec F2 n
  | _, nil, nil => nil
  | _, cons a as, cons b bs => cons (F2.add a b) (add as bs)
end Vec

-- testing addition
#reduce Vec.add (Vec.cons F2.zero Vec.nil) (Vec.cons F2.one Vec.nil)
#reduce Vec.add (Vec.cons F2.zero (Vec.cons F2.one Vec.nil)) (Vec.cons F2.one (Vec.cons F2.one Vec.nil))

-- Now we can define the nim game
def nim (n : ℕ) : Type := Vec F2 n

-- We can define the nim sum (the vector addition)
def nim_sum : nim n → nim n → nim n := Vec.add
