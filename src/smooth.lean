import algebra.ring
import algebra.field
import order
import tactic

universe u

def nilpotent {α} [semigroup α] [has_zero α] (x : α) := x * x = 0
def D (α : Type u) [semigroup α] [has_zero α] := {x : α // nilpotent x}

instance D_has_coe_to_α (α : Type u) [semigroup α] [has_zero α] : has_coe (D α) α :=
  ⟨λ d, d.val⟩

instance (α : Type u) [ring α] : has_zero (D α) :=
  ⟨⟨0, zero_mul 0⟩⟩

@[simp]
lemma D.zero_coe (α : Type u) [ring α] : ((0:D α) : α) = (0 : α) := rfl

def microaffine {α} [ring α] (f : D α → α) (a : α) := ∀ d, f d = f 0 + a * d

@[protect_proj] class SAI_model (α : Type u) extends field α, linear_order α :=
(sqrt : α → α) 
(sqrt_prop : ∀ x, 0 < x → sqrt x * sqrt x = x)
(kl : (D α → α) → α)
(kl_prop : ∀ f, microaffine f (kl f))
(kl_unique : ∀ f a, microaffine f a → a = kl f) 

def kl {α} [SAI_model α] : (D α → α) → α := SAI_model.kl
def kl_prop {α} [SAI_model α] (f : D α → α) : microaffine f (kl f) := SAI_model.kl_prop f
def kl_unique {α} [SAI_model α] (f : D α → α) (a : α) (h : microaffine f a) : a = kl f := SAI_model.kl_unique f a h

lemma non_classical (em : ∀ P, P ∨ ¬ P) (𝕄 : Type) [h : SAI_model 𝕄] : ∀ x, nilpotent x → x = 0 :=
  begin
    intros x nil_x,
    have x_z : x = 0 ∨ x ≠ 0, by apply em,
    cases x_z, {assumption}, exfalso,
    have x_ineq_z : (x < 0 ∨ x > 0), exact ne.lt_or_lt x_z,
    unfold nilpotent at *,
    cases x_ineq_z,
    all_goals {have xx_gt_0 : x * x > 0, by finish, finish},
  end

lemma microcancellation (α) [M:SAI_model α] (x y : α) ( H : ∀ d : D α, x * d = y * d) : x = y :=
  begin
    let f : D α → α := λ d, x * d,
    have f_x : ∀ d, f d = x * d, by {intro d, refl},
    have f_y : ∀ d, f d = y * d, by {intro d, rw ← H d},
    transitivity (SAI_model.kl f),
    {apply kl_unique, intro d, simp_rw f_x, simp},
    {symmetry, apply kl_unique, intro d, simp_rw f_y, simp },
  end

def deriv {α} [M:SAI_model α] := λ (f : α → α) (a : α), kl (λ d, f (a + ↑d))

lemma deriv_prop {α} [M:SAI_model α] (f : α → α) (x) : ∀ d : D α, f (x + d) = f x + deriv f x * d :=
  begin
    let g := λ d : D α, f (a + ↑d)
  end

lemma deriv_unique {α} [M:SAI_model α] (f : α → α) (x) (y) ( H : ∀ d : D α, f (x + d) = f x + y * d) : y = deriv f x

lemma deriv_sum {α} [M:SAI_model α] (f g : α → α) : deriv (λ x, f x + g x) = λ x, deriv f x + deriv g x :=
  begin
    unfold deriv,
    funext,

  end