import data.real.basic

structure complex :=
(re : ℝ)
(im : ℝ)

-- type ℝ as \R
-- type ℂ as \com or \Com

notation `ℂ` := complex

namespace complex

@[extensionality] lemma ext (x y : ℂ) (h₁ : x.re = y.re) (h₂ : x.im = y.im) :
  x = y :=
begin
  cases x, cases y,
  congr,
  { assumption },
  { assumption }
end

def add (x y : ℂ) : ℂ :=
{ re := x.re + y.re,
  im := x.im + y.im }

instance : has_add ℂ := ⟨add⟩

@[simp] lemma add_re (x y : ℂ) :
  (x + y).re = x.re + y.re :=
rfl

@[simp] lemma add_im (x y : ℂ) :
  (x + y).im = x.im + y.im :=
rfl

instance : add_semigroup ℂ :=
{ add_assoc :=
  begin
    intros x y z,
    ext,
    { simp },
    { simp }
  end,
  .. complex.has_add }

def zero : ℂ := ⟨0, 0⟩

def one : ℂ := ⟨1, 0⟩ 
/-
Exercise:
* define zero, one, negation, multiplication
* define the corresponding instances has_zero, has_one, has_neg, has_mul
  (this will unlock notation, so you can now use 0, 1, -, *).
* show that ℂ is a commutative ring by un-sorry-ing

instance : comm_ring ℂ :=
sorry

-/

end complex

namespace clean
/-
Exercise:
* define your own copy of the natural numbers
-/

inductive nat
| zero : nat
| succ : nat → nat

-- At this point ℕ (type as \N) still refers to the natural numbers that are already defined in Lean.
#print notation ℕ

-- Now we overwrite this notation
local notation `ℕ` := nat
#print notation ℕ

namespace nat
/-
We do not automatically get access to the numerals 0, 1, 2, 3, ...
To do that, we need to define 0, 1, and +.
-/

instance : has_zero ℕ := ⟨zero⟩

instance : has_one ℕ := ⟨succ zero⟩

-- Addition is a bit trickier to define. It is defined by induction.
-- Can you finish this definition?
def add : ℕ → ℕ → ℕ
| n zero     := _
| n (succ m) := _

instance : has_add ℕ := ⟨add⟩

-- Lean can now automagically make sense of the numeral 2.
#check (2 : ℕ) + 2

-- If you correctly filled in the definition of add,
-- then this lemma should be "true by reflexivity (rfl) of equality"
-- a.k.a. "true by definition".
lemma two_add_two : (2 : ℕ) + 2 = 4 := rfl

-- One of the following two lemmas is true by definition.
-- The other needs to be proven by induction.
@[simp] lemma add_zero (n : ℕ) : n + 0 = n := _

@[simp] lemma zero_add (n : ℕ) : 0 + n = n := _

/-
Exercise: define an instance of add_comm_group ℕ.

instance : add_comm_group ℕ :=
{ }
-/

/-
Exercise: define an instance of comm_semiring ℕ
-/

end nat

end clean