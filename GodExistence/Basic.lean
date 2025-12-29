import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace GodExistence

structure Model where
  World : Type u
  Rel : World → World → Prop


namespace Model

variable {K : Model}

instance : CoeSort Model (Type u) := ⟨Model.World⟩
instance : CoeFun Model (λ K => K.World → K.World → Prop) := ⟨Model.Rel⟩

class IsReflexive (K : Model) : Prop where
  refl : ∀ {x : K}, K x x
export IsReflexive (refl)
attribute [grind .] refl

class IsTransitive (K : Model) : Prop where
  trans: ∀ {x y z : K}, K x y → K y z → K x z
export IsTransitive (trans)
attribute [grind <=] trans

class IsSymmetric (K : Model) : Prop where
  symm : ∀ {x y : K}, K x y → K y x
export IsSymmetric (symm)
attribute [grind <=] symm

class IsEuclidean (K : Model) : Prop where
  eucl : ∀ {x y z : K}, K x y → K x z → K y z
export IsEuclidean (eucl)

class IsKTB (K : Model) extends K.IsReflexive, K.IsSymmetric where
class IsKB4 (K : Model) extends K.IsSymmetric, K.IsTransitive where
class IsS4 (K : Model) extends K.IsReflexive, K.IsTransitive where
class IsS5 (K : Model) extends K.IsReflexive, K.IsSymmetric, K.IsTransitive where

instance [K.IsKB4] : K.IsEuclidean where
  eucl {x y z} Rxy Rxz := by
    exact K.trans (K.symm Rxy) Rxz;

instance [K.IsS5] : K.IsKB4 where

instance [K.IsS5] : K.IsEuclidean := instIsEuclideanOfIsKB4

end Model


abbrev Formula (K : Model) := Set K

/-- Statement about being (`α`) -/
abbrev Property (α) (K : Model) := α → Formula K

namespace Formula

variable {K : Model} {x : K} {φ ψ : Formula K} {Φ : Property α K}

@[simp] def falsum : Formula K := λ _ => False
notation:max "⊥ₘ" => falsum

@[simp] def verum : Formula K := λ _ => True
notation:max "⊤ₘ" => verum

@[grind] def neg (φ : Formula K) : Formula K := λ x => ¬(φ x)
prefix:80 "∼" => neg

@[simp] lemma eq_negverum_falsum : ∼(⊤ₘ : Formula K) = ⊥ₘ := by funext x; simp [verum, falsum, neg];
@[simp] lemma eq_negfalsum_verum : ∼(⊥ₘ : Formula K) = ⊤ₘ := by funext x; simp [verum, falsum, neg];

@[simp, grind .] lemma not_falsum : ¬(⊥ₘ x) := by simp [falsum];
@[simp, grind .] lemma always_verum : ⊤ₘ x := by simp [verum];


@[grind] def and (φ ψ : Formula K) : Formula K := λ x => φ x ∧ ψ x
infixl:75 " ⋏ " => and

@[grind] def or (φ ψ : Formula K) : Formula K := λ x => φ x ∨ ψ x
infixl:74 " ⋎ " => or

@[simp, grind] def imp (φ ψ : Formula K) : Formula K := λ x => φ x → ψ x
infixr:66 " ➝ " => imp

@[grind] def iff (φ ψ : Formula K) : Formula K := λ x => φ x ↔ ψ x
infix:65 " ⭤ " => iff

@[grind] def all (Φ : Property α K) : Formula K := λ x => ∀ a, Φ a x
prefix:80 "∀'" => all

@[grind] def ex (Φ : Property α K) : Formula K := λ x => ∃ a, Φ a x
prefix:80 "∃'" => ex

@[grind] def box (φ : Formula K) : Formula K := λ x => ∀ y, K x y → φ y
prefix:80 "□" => box

@[grind] def dia (φ : Formula K) : Formula K := λ x => ∃ y, K x y ∧ φ y
prefix:80 "◇" => dia


@[grind =] lemma eq_negbox_dianeg : ∼(□φ) = ◇(∼φ) := by funext x; grind;
@[grind =] lemma eq_negall_exneg : ∼(∀' Φ) = ∃' (λ a => ∼(Φ a)) := by funext x; grind;


def Valid (φ : Formula K) : Prop := ∀ x, φ x
prefix:60 "⊧ " => Valid

end Formula



namespace Property

abbrev neg (Φ : Property α K) : Property α K := λ a => ∼(Φ a)
prefix:80 "∼ₚ" => neg

end Property

/-- Statement about `Property` -/
abbrev Metaproperty (α) (K : Model) := (Property α K) → Formula K


section

variable {K : Model} {φ ψ : Formula K}

@[grind .]
lemma valid_axiomT [K.IsReflexive] : ⊧ □φ ➝ φ := by
  intro x hx;
  apply hx;
  exact K.refl;

@[grind .]
lemma valid_axiomTDual [K.IsReflexive] : ⊧ φ ➝ ◇φ := by
  intro x hx;
  use x;
  constructor;
  . exact K.refl;
  . exact hx;

@[grind .]
lemma valid_axiomFour [K.IsTransitive] : ⊧ □φ ➝ □□φ := by
  intro x hx y Rxy z Ryz;
  apply hx;
  exact K.trans Rxy Ryz;

@[grind .]
lemma valid_axiomB [K.IsSymmetric] : ⊧ ◇□φ ➝ φ := by
  intro x hx;
  obtain ⟨y, Rxy, hy⟩ : (◇□φ) x := hx;
  apply hy;
  exact K.symm Rxy;

@[grind .]
lemma valid_axiomFive [K.IsEuclidean] : ⊧ ◇□φ ➝ □φ := by
  intro x hx y Rxy;
  obtain ⟨z, Rxz, hz⟩ : (◇□φ) x := hx;
  apply hz;
  exact K.eucl Rxz Rxy;

example [K.IsKB4] : ⊧ ◇□φ ➝ □φ := valid_axiomFive
example [K.IsS5] : ⊧ ◇□φ ➝ □φ := valid_axiomFive

@[grind →]
lemma valid_mdp (h₁ : ⊧ φ ➝ ψ) (h₂ : ⊧ φ) : ⊧ ψ := fun x => h₁ x $ h₂ x

end


section Argument

variable
  {α} {K : Model}
  {Φ Ψ : Property α K}

variable {Positive : Metaproperty α K}

/-- Emptyness is non-positive. -/
lemma emptyness_negative
  (Ax1 : ∀ Φ : Property α K, ⊧ Positive (λ a => ∼(Φ a)) ⭤ ∼Positive Φ)
  (Ax2 : ∀ Φ Ψ : Property α K, ⊧ Positive Φ ➝ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Ψ)
  : ⊧ ∼Positive (λ _ => ⊥ₘ) := by
  intro x;

  by_contra! hC;
  replace hC : x ∈ Positive (λ _ => ⊥ₘ) := not_not.mp $ Set.mem_compl_iff _ _ |>.not.mp hC;

  have : x ∈ ∼Positive (λ _ => ⊤ₘ) := Ax1 _ x |>.mp (by simpa);
  have : x ∈ Positive (λ _ => ⊤ₘ) := Ax2 (λ _ => ⊥ₘ) _ _ ?_ ?_;
  contradiction;
  . assumption;
  . grind;

/-- Positive properties are possibly exemplified. -/
lemma theorem1
  (Ax1 : ∀ Φ : Property α K, ⊧ Positive (λ a => ∼(Φ a)) ⭤ ∼Positive Φ)
  (Ax2 : ∀ Φ Ψ : Property α K, ⊧ Positive Φ ➝ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Ψ)
  : ⊧ Positive Φ ➝ ◇∃' (λ a => Φ a) := by
  intro x hx;
  have : (∼□∀'(λ a => Φ a ➝ ⊥ₘ)) x := (not_imp_not.mpr $ Ax2 Φ (λ _ => ⊥ₘ) x hx) $ by apply emptyness_negative Ax1 Ax2;
  grind;

def Godlike (Positive : Metaproperty α K) : Property α K := λ a => ∀' (λ Φ => Positive Φ ➝ Φ a)

/-- Possibly, God exists. -/
lemma possibly_exists_godlike
  (Ax1 : ∀ Φ : Property α K, ⊧ Positive (λ a => ∼(Φ a)) ⭤ ∼Positive Φ)
  (Ax2 : ∀ Φ Ψ : Property α K, ⊧ Positive Φ ➝ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Ψ)
  (Ax3 : ⊧ Positive (Godlike (Positive)))
  : ⊧ ◇(∃' (λ (a : α) => Godlike (Positive := Positive) a)) := by
  intro x;
  apply theorem1 Ax1 Ax2;
  apply Ax3;

def Essence (Φ : Property α K) : Property α K := λ a => Φ a ⋏ ∀' (λ Ψ : Property α K => Ψ a ➝ □(∀' (λ b => Φ b ➝ Ψ b)))

/-- Being Godlike is an essence of any Godlike being -/
lemma godlike_ess
  (Ax1 : ∀ Φ : Property α K, ⊧ Positive (λ a => ∼(Φ a)) ⭤ ∼Positive Φ)
  (Ax4 : ∀ Φ : Property α K, ⊧ Positive Φ ➝ □Positive Φ)
  : ⊧ ∀' (λ a => Godlike (Positive := Positive) a ➝ Essence (Godlike (Positive := Positive)) a) := by
  intro x a ha;
  constructor;
  . assumption;
  . intro Ψ hΨ y Rxy b b_godlike_y;
    have Ψ_positive_x : x ∈ Positive Ψ := by
      by_contra! hC;
      have : Positive (∼Ψ ·) x := Ax1 Ψ x |>.mpr hC;
      have : (∼Ψ a) x := ha _ this;
      contradiction;
    apply b_godlike_y;
    apply Ax4 _ x Ψ_positive_x y Rxy;

def NecessaryExistence : Property α K := λ a => ∀' (λ Φ : Property α K => Essence Φ a ➝ □∃' (λ b => Φ b))

theorem necessary_exists_godlike
  [K.IsS5]
  (Ax1 : ∀ Φ : Property α K, ⊧ Positive (λ a => ∼(Φ a)) ⭤ ∼Positive Φ)
  (Ax2 : ∀ Φ Ψ : Property α K, ⊧ Positive Φ ➝ □(∀' (λ a => Φ a ➝ Ψ a)) ➝ Positive Ψ)
  (Ax3 : ⊧ Positive (Godlike (Positive := Positive)))
  (Ax4 : ∀ Φ : Property α K, ⊧ Positive Φ ➝ □Positive Φ)
  (Ax5 : ⊧ Positive NecessaryExistence)
  : ⊧ □∃' (λ a => Godlike (α := α) (K := K) (Positive := Positive) a) := by
  suffices ⊧ ◇□∃' (λ a => Godlike (Positive := Positive) a) by apply valid_mdp valid_axiomFive this;
  intro x;
  obtain ⟨y, Rxy, ⟨a, a_godlike_y⟩⟩ : (◇∃'(λ a => Godlike _ a)) x := possibly_exists_godlike Ax1 Ax2 Ax3 x;
  use y;
  constructor;
  . assumption;
  . have H₁ := a_godlike_y NecessaryExistence;
    have : NecessaryExistence a y := H₁ $ Ax5 y;
    apply this;
    apply godlike_ess Ax1 Ax4 y a a_godlike_y;

end Argument


end GodExistence
