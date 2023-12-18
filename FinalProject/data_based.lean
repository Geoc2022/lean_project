import Mathlib.Tactic

namespace surreal


inductive number : Type where
| mk : List number → List number → number

def list_set : List number → Set number
| [] => ∅
| x :: xs => list_set xs ∪ {x}


-- Let's test this with the simplest number - zero
def zero : number := number.mk [] []


def number.left : number → Set number
| (number.mk L _) => list_set L

def number.right : number → Set number
| (number.mk _ R) => list_set R

-- Let's test zero has no left or right elements
#reduce zero.left
#reduce zero.right


-- def number.le : number → number → Prop
--   | (mk [] []), (mk [] []) => true
--   | (mk (xl :: Xl) Xr), y => ¬(y.le xl) ∧ ((mk Xl Xr).le y)
--   | (mk Xl (xr :: Xr)), y => ((mk Xl Xr).le y)
--   | x, (mk (yl :: Yl) Yr) => (x.le (mk Yl Yr))
--   | x, (mk Yl (yr :: Yr)) => ¬(yr.le x) ∧ (x.le (mk Yl Yr))
-- decreasing_by sorry

-- The 2nd axiom is implicit in this definition
mutual
  -- lex is ment to be the analgoue of ≱ in the book
  def lex1 : number → List number → Prop
    | _, [] => true
    | x, l :: L => ¬(x.le l) ∧ (lex1 x L)
  def lex2 : List number → number → Prop
    | [], _  => true
    | l :: L, x => ¬(l.le x) ∧ (lex2 L x)

  def number.le : number → number → Prop
    | (number.mk XL XR), (number.mk YL YR) => (lex1 (number.mk YL YR) XL) ∧ (lex2 YR (number.mk XL XR))
end
decreasing_by sorry

def number.surreal : number → Prop
  | n => ∀l ∈ n.left, ∀r ∈ n.right, ¬(l.le r)

-- unfortunately, this does not reduce
#reduce number.le zero zero

-- but we can still write other numbers
def one : number := number.mk [zero] []
def minus_one : number := number.mk [] [zero]
def two : number := number.mk [one] []
def star : number := number.mk [zero] [zero]

-- and define functions like addition
mutual
  def number.add : number → number → number
    | (number.mk XL XR), (number.mk YL YR) => number.mk ((Nlist_add XL (number.mk YL YR)) ++ (Nlist_add YL (number.mk XL XR))) ((Nlist_add XR (number.mk YL YR)) ++ (Nlist_add YR (number.mk XL XR)))
  def Nlist_add : List number → number → List number
    | [], y => []
    | x :: xs, y => (x.add y) :: (Nlist_add xs y)
end
decreasing_by sorry
