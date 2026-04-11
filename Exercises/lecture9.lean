/-
  Chapter 11: The Fundamental Theorem of Identity Types
  From: Introduction to Homotopy Type Theory, Egbert Rijke
  -------------------------------------------------------
  Lean 4 implementation — M782, Lecture 9.

  Under Lean's UIP, path algebra and coherence are trivial. We focus on:
    - Families of equivalences and tot (11.1)
    - The Fundamental Theorem of Identity Types (11.2)
    - Equality on the natural numbers (11.3)
    - Embeddings (11.4)
    - Disjointness of coproducts (11.5)
    - The Structure Identity Principle (11.6)
-/

universe u v w u₁ u₂ u₃ u₄

-- ============================================================================
-- Imports from lecture 8
-- ============================================================================

/-- sec(f) := Σ(g : B → A) f ∘ g ~ id_B -/
structure Section (f : α → β) where
  inv      : β → α
  rightInv : ∀ b, f (inv b) = b

/-- retr(f) := Σ(h : B → A) h ∘ f ~ id_A -/
structure Retraction (f : α → β) where
  inv     : β → α
  leftInv : ∀ a, inv (f a) = a

/-- is-equiv(f) := sec(f) × retr(f) -/
structure IsEquiv (f : α → β) where
  sec  : Section f
  retr : Retraction f

/-- A ≃ B := Σ(f : A → B) is-equiv(f) -/
structure Equiv (α : Type u) (β : Type v) where
  toFun   : α → β
  isEquiv : IsEquiv toFun

infixl:25 " ≃ " => Equiv

namespace Equiv

def secFun   (e : α ≃ β) : β → α := e.isEquiv.sec.inv
def retrFun  (e : α ≃ β) : β → α := e.isEquiv.retr.inv
def right_inv (e : α ≃ β) : ∀ b, e.toFun (e.secFun b) = b   := e.isEquiv.sec.rightInv
def left_inv  (e : α ≃ β) : ∀ a, e.retrFun (e.toFun a) = a  := e.isEquiv.retr.leftInv

protected def mk' {α : Type u} {β : Type v}
    (f : α → β) (g : β → α)
    (linv : ∀ a, g (f a) = a) (rinv : ∀ b, f (g b) = b) : α ≃ β :=
  { toFun   := f
    isEquiv := { sec := ⟨g, rinv⟩, retr := ⟨g, linv⟩ } }

protected def refl (α : Type u) : α ≃ α :=
  Equiv.mk' id id (fun _ => rfl) (fun _ => rfl)

protected def symm (e : α ≃ β) : β ≃ α :=
  { toFun   := e.retrFun
    isEquiv := {
      sec  := ⟨e.toFun, e.left_inv⟩
      retr := ⟨e.toFun, fun b => by
        have : e.retrFun b = e.secFun b :=
          calc e.retrFun b
              _ = e.retrFun (e.toFun (e.secFun b)) := congrArg e.retrFun (e.right_inv b).symm
              _ = e.secFun b := e.left_inv (e.secFun b)
        rw [this, e.right_inv]⟩ } }

protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  { toFun   := e₂.toFun ∘ e₁.toFun
    isEquiv := {
      sec  := ⟨e₁.secFun ∘ e₂.secFun, fun c => by
        show e₂.toFun (e₁.toFun (e₁.secFun (e₂.secFun c))) = c
        rw [e₁.right_inv, e₂.right_inv]⟩
      retr := ⟨e₁.retrFun ∘ e₂.retrFun, fun a => by
        show e₁.retrFun (e₂.retrFun (e₂.toFun (e₁.toFun a))) = a
        rw [e₂.left_inv, e₁.left_inv]⟩ } }

instance : Trans (α := Type u) (β := Type v) (γ := Type w) Equiv Equiv Equiv where
  trans := Equiv.trans

end Equiv

def IsEquiv.ofInverse {f : α → β} (g : β → α)
    (rinv : ∀ b, f (g b) = b) (linv : ∀ a, g (f a) = a) : IsEquiv f :=
  { sec := ⟨g, rinv⟩, retr := ⟨g, linv⟩ }


-- ============================================================================
-- Section 10.1: Contractible types
-- ============================================================================

structure IsContr (α : Type u) where
  center      : α
  contraction : ∀ x, center = x

-- ============================================================================
-- Example: Unit is contractible
-- ============================================================================

def isContrUnit : IsContr Unit :=
  ⟨(), fun () => rfl⟩

-- ============================================================================
-- Example: Σ(x : A) a = x is contractible
-- ============================================================================

def isContrTotalPath {α : Type u} (a : α) : IsContr (Σ x, PLift (a = x)) :=
  ⟨⟨a, PLift.up rfl⟩, fun ⟨x, ⟨p⟩⟩ => by subst p; rfl⟩

-- ============================================================================
-- Section 10.2: Singleton induction
-- ============================================================================

def evPt {α : Type u} (a : α) {B : α → Sort v} (f : (x : α) → B x) : B a := f a

def IsSingleton.{u₁', u₂'} {α : Type u₁'} (a : α) :=
  (B : α → Type u₂') → Section (evPt a (B := B))

def contrToSingleton.{u₁', u₂'} {α : Type u₁'} {a : α}
    (h : IsContr α) : IsSingleton.{u₁', u₂'} a := by
  intro B
  let C := h.contraction
  have C' : (x : α) → a = x := fun x => (C a).symm.trans (C x)
  exact ⟨
    fun b x => C' x ▸ b,
    fun b => rfl
    ⟩

def singletonToContr {α : Type u} {a : α}
    (sing : IsSingleton.{u, 0} a) : IsContr α :=
  sorry

-- ============================================================================
-- Section 10.3: Fibers of maps
-- ============================================================================

def Fib {α : Type u} {β : Type v} (f : α → β) (b : β) := PSigma (fun a => f a = b)

theorem fib_eq {α : Type u} {β : Type v} {f : α → β} {b : β} {s t : Fib f b}
    (h : s.1 = t.1) : s = t := by
  cases s with | mk a p => cases t with | mk a' q => simp at h; subst h; rfl

-- ============================================================================
-- Section 10.4: Contractible maps
-- ============================================================================

def IsContrMap {α : Type u} {β : Type v} (f : α → β) := ∀ b, IsContr (Fib f b)

def isEquivOfContrMap {α : Type u} {β : Type v} {f : α → β}
    (cf : IsContrMap f) : IsEquiv f :=
  IsEquiv.ofInverse
    sorry
    sorry
    sorry

-- ============================================================================
-- Section 10.5: Coherently invertible maps
-- ============================================================================

structure HasInverse (f : α → β) where
  inv  : β → α
  rinv : ∀ b, f (inv b) = b
  linv : ∀ a, inv (f a) = a

structure IsCohInvertible (f : α → β) extends HasInverse f where
  coherence : ∀ a, rinv (f a) = congrArg f (linv a)

def IsEquiv.ofHasInverse {f : α → β} (h : HasInverse f) : IsEquiv f :=
  IsEquiv.ofInverse h.inv h.rinv h.linv

def HasInverse.ofIsEquiv {f : α → β} (e : IsEquiv f) : HasInverse f :=
  let g := e.sec.inv
  let G := e.sec.rightInv
  let h := e.retr.inv
  let H := e.retr.leftInv
  { inv  := g
    rinv := G
    linv := sorry }

def IsCohInvertible.ofHasInverse {f : α → β} (h : HasInverse f)
    : IsCohInvertible f :=
  { h with coherence := fun _ => rfl }

def IsCohInvertible.ofIsEquiv {f : α → β} (e : IsEquiv f)
    : IsCohInvertible f :=
  IsCohInvertible.ofHasInverse (HasInverse.ofIsEquiv e)

-- ============================================================================
-- MAIN THEOREM: Any equivalence has contractible fibers
-- ============================================================================

def isContrMapOfCohInvertible {α : Type u} {β : Type v} {f : α → β}
    (ci : IsCohInvertible f) : IsContrMap f :=
  sorry

def isContrMapOfIsEquiv {α : Type u} {β : Type v} {f : α → β}
    (e : IsEquiv f) : IsContrMap f :=
  isContrMapOfCohInvertible (IsCohInvertible.ofIsEquiv e)

def isContrTotalPath'ViaEquiv (a : α) : IsContr (Fib id a) :=
  isContrMapOfIsEquiv (Equiv.refl α).isEquiv a

-- ============================================================================
-- A type is contractible iff it is equivalent to Unit
-- ============================================================================

def equivUnitOfIsContr {α : Type u} (h : IsContr α) : α ≃ Unit :=
  sorry

def isContrOfEquivUnit {α : Type u} (e : α ≃ Unit) : IsContr α :=
  sorry

-- ============================================================================
-- Closure properties of contractible types
-- ============================================================================

theorem eq_of_isContr {α : Type u} (h : IsContr α) {x y : α} : x = y :=
  (h.contraction x).symm ▸ h.contraction y

structure IsRetractOf (α : Type u) (β : Type v) where
  section_ : α → β
  retract  : β → α
  isRetr   : ∀ a, retract (section_ a) = a

def isContrRetractOf {α : Type u} {β : Type v}
    (r : IsRetractOf α β) (hB : IsContr β) : IsContr α :=
  sorry

def isContrOfEquiv {α : Type u} {β : Type v}
    (f : α → β) (e : IsEquiv f) (hB : IsContr β) : IsContr α :=
  isContrRetractOf ⟨f, e.retr.inv, e.retr.leftInv⟩ hB

def isContrOfEquiv' {α : Type u} {β : Type v}
    (f : α → β) (e : IsEquiv f) (hA : IsContr α) : IsContr β :=
  isContrRetractOf ⟨e.sec.inv, f, e.sec.rightInv⟩ hA

def isEquivOfIsContr {α : Type u} {β : Type v}
    (f : α → β) (hA : IsContr α) (hB : IsContr β) : IsEquiv f :=
  sorry

def equivOfIsContr {α : Type u} {β : Type v}
    (hA : IsContr α) (hB : IsContr β) : α ≃ β :=
  sorry

def isContrSigma {α : Type u} {B : α → Type v}
    (hA : IsContr α) (hB : IsContr (B hA.center)) : IsContr (Σ x, B x) :=
  sorry

def isContrSigma' {α : Type u} {B : α → Type v}
    (hA : IsContr α) (hB : ∀ x, IsContr (B x)) : IsContr (Σ x, B x) :=
  isContrSigma hA (hB hA.center)

def isPropIsContr {α : Type u} (h : IsContr α) (x y : α)
    : IsContr (PLift (x = y)) :=
  ⟨PLift.up (eq_of_isContr h), fun ⟨_⟩ => rfl⟩

def isContrPi {α : Type u} {B : α → Type v}
    (hB : ∀ x, IsContr (B x)) : IsContr ((x : α) → B x) :=
  sorry

def isContrFunctionType {α : Type u} {β : Type v}
    (hB : IsContr β) : IsContr (α → β) :=
  isContrPi (fun _ => hB)

def isContrIsContr {α : Type u} (h : IsContr α) : IsContr (IsContr α) :=
  sorry

theorem isPropIsContr' {α : Type u} (h k : IsContr α) : h = k :=
  sorry


-- ============================================================================
-- ============================================================================
--
--    CHAPTER 11: THE FUNDAMENTAL THEOREM OF IDENTITY TYPES
--
-- ============================================================================
-- ============================================================================


-- ============================================================================
-- Section 11.1: Families of equivalences
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Definition 11.1.1: The map tot(f)
-- Given a family of maps f : Π(x:A) B(x) → C(x),
-- tot(f) : Σ(x:A) B(x) → Σ(x:A) C(x)
-- by tot(f)(x, y) := (x, f(x, y))
-- ----------------------------------------------------------------------------

def tot {α : Type u} {B : α → Type v} {C : α → Type w}
    (f : (x : α) → B x → C x)
    : (Σ x, B x) → (Σ x, C x)
  | ⟨x, y⟩ => ⟨x, f x y⟩

-- ----------------------------------------------------------------------------
-- Lemma 11.1.2: fib_{tot(f)}(t) ≃ fib_{f(pr1(t))}(pr2(t))
-- ----------------------------------------------------------------------------

def fibTotEquivFibFiberwise
    {α : Type u} {B : α → Type v} {C : α → Type w}
    (f : (x : α) → B x → C x) (t : Σ x, C x)
    : Fib (tot f) t ≃ Fib (f t.1) t.2 := by
  sorry

-- ----------------------------------------------------------------------------
-- Theorem 11.1.3: A family of maps f is a family of equivalences
-- iff tot(f) is an equivalence.
-- ----------------------------------------------------------------------------

-- (i) → (ii): If each f(x) is an equivalence, then tot(f) is
def isEquivTotOfIsEquivFiberwise
    {α : Type u} {B : α → Type v} {C : α → Type w}
    {f : (x : α) → B x → C x}
    (H : ∀ x, IsEquiv (f x))
    : IsEquiv (tot f) :=
  sorry

-- (ii) → (i): If tot(f) is an equivalence, then each f(x) is
def isEquivFiberwiseOfIsEquivTot
    {α : Type u} {B : α → Type v} {C : α → Type w}
    {f : (x : α) → B x → C x}
    (eTot : IsEquiv (tot f))
    : ∀ x, IsEquiv (f x) :=
  sorry

-- ----------------------------------------------------------------------------
-- Lemma 11.1.4: σ-map
-- If f : A → B is an equivalence and C is a type family over B,
-- then σ_f(C) := λ(x,z).(f(x),z) : Σ(x:A) C(f(x)) → Σ(y:B) C(y)
-- is an equivalence.
-- ----------------------------------------------------------------------------

def σMap {α : Type u} {β : Type v} (f : α → β) (C : β → Type w)
    : (Σ x, C (f x)) → (Σ y, C y)
  | ⟨x, z⟩ => ⟨f x, z⟩

def isEquivσMap
    {α : Type u} {β : Type v} (f : α → β) (C : β → Type w)
    (ef : IsEquiv f) : IsEquiv (σMap f C) :=
  sorry

-- ----------------------------------------------------------------------------
-- Definition 11.1.5 & Theorem 11.1.6: Generalized total map tot_f(g)
-- ----------------------------------------------------------------------------

def totOver {α : Type u} {β : Type v} {C : α → Type u₁} {D : β → Type u₂}
    (f : α → β) (g : (x : α) → C x → D (f x))
    : (Σ x, C x) → (Σ y, D y)
  | ⟨x, z⟩ => ⟨f x, g x z⟩

def isEquivTotOverOfIsEquivFiberwise
    {α : Type u} {β : Type v} {C : α → Type u₁} {D : β → Type u₂}
    {f : α → β} {g : (x : α) → C x → D (f x)}
    (ef : IsEquiv f)
    (eg : ∀ x, IsEquiv (g x))
    : IsEquiv (totOver f g) :=
  sorry


-- ============================================================================
-- Section 11.2: The Fundamental Theorem of Identity Types
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Definition 11.2.1: Identity systems
-- ----------------------------------------------------------------------------

def IsIdentitySystem.{u₅, u₆, u₇} {α : Type u₅} (a : α) {B : α → Type u₆} (b : B a) :=
  (P : (x : α) → B x → Type u₇) →
    Section (fun (h : (x : α) → (y : B x) → P x y) => h a b)

-- Example: The canonical identity system B(x) := (a = x), b := rfl
-- (omitted due to universe issues with Prop-valued identity types)

-- ----------------------------------------------------------------------------
-- Theorem 11.2.2: The Fundamental Theorem of Identity Types (FTIT)
-- ----------------------------------------------------------------------------

-- (ii) → (i): If Σ B is contractible, then f is a family of equivs
def fundamentalTheoremId
    {α : Type u} {a : α} {B : α → Type v}
    (f : (x : α) → (a = x) → B x)
    (hContrB : IsContr (Σ x, B x))
    : ∀ x, IsEquiv (f x) :=
  sorry

-- (i) → (ii): If f is a family of equivs, then Σ B is contractible
def fundamentalTheoremId'
    {α : Type u} {a : α} {B : α → Type v}
    (f : (x : α) → (a = x) → B x)
    (ef : ∀ x, IsEquiv (f x))
    : IsContr (Σ x, B x) :=
  sorry

-- Corollary
def fundamentalTheoremIdCanonical
    {α : Type u} {a : α} {B : α → Type v} (b : B a)
    (hContrB : IsContr (Σ x, B x))
    : ∀ x, IsEquiv (fun (p : a = x) => p ▸ b) :=
  fundamentalTheoremId (fun x p => p ▸ b) hContrB

-- (ii) → (iii): Contractible total space → identity system
def isIdentitySystemOfIsContrTotal
    {α : Type u} {a : α} {B : α → Type v} {b : B a}
    (c : IsContr (Σ x, B x))
    : IsIdentitySystem.{u, v, w} a b :=
  sorry

-- (iii) → (ii): Identity system → contractible total space
def isContrTotalOfIsIdentitySystem
    {α : Type u} {a : α} {B : α → Type v} {b : B a}
    (isId : IsIdentitySystem.{u, v, max u v} a b)
    : IsContr (Σ x, B x) :=
  sorry


-- ============================================================================
-- Section 11.3: Equality on the natural numbers
-- ============================================================================

-- Observational equality Eq-ℕ (as Type, not Prop, so it works with Σ)
def EqNat : Nat → Nat → Type
  | 0,     0     => Unit
  | 0,     _+1   => Empty
  | _+1,   0     => Empty
  | m+1,   n+1   => EqNat m n

def reflEqNat : (m : Nat) → EqNat m m
  | 0     => ()
  | m+1   => reflEqNat m

-- The canonical map (m = n) → EqNat(m, n)
def eqToEqNat {m n : Nat} (p : m = n) : EqNat m n :=
  p ▸ reflEqNat m

-- Theorem 11.3.1: (m = n) ≃ EqNat(m, n)
-- By FTIT, it suffices to show Σ(n:ℕ) EqNat(m, n) is contractible.

def succEqNat (m : Nat) : (Σ n, EqNat m n) → (Σ n, EqNat (m+1) n)
  | ⟨n, e⟩ => ⟨n+1, e⟩

def isContrTotalEqNat : (m : Nat) → IsContr (Σ n, EqNat m n)
  | 0 => ⟨⟨0, ()⟩, fun ⟨n, e⟩ => by
      cases n with
      | zero => exact Sigma.mk.injEq _ _ _ _ ▸ rfl
      | succ n => exact Empty.elim e⟩
  | m+1 =>
    let ih := isContrTotalEqNat m
    ⟨⟨m+1, reflEqNat m⟩, fun ⟨n, e⟩ => by
      cases n with
      | zero => exact Empty.elim e
      | succ n =>
        have := ih.contraction ⟨n, e⟩
        have hm := ih.contraction ⟨m, reflEqNat m⟩
        exact congrArg (succEqNat m) (hm.symm.trans this)⟩

-- Apply the FTIT
def isEquivEqToEqNat (m : Nat) : ∀ n, IsEquiv (@eqToEqNat m n) :=
  fundamentalTheoremId (fun n p => eqToEqNat p) (isContrTotalEqNat m)

-- The inverse: EqNat(m, n) → (m = n)
def eqNatToEq : (m n : Nat) → EqNat m n → m = n
  | 0,     0,     _  => rfl
  | 0,     _+1,   h  => Empty.elim h
  | _+1,   0,     h  => Empty.elim h
  | m+1,   n+1,   h  => congrArg Nat.succ (eqNatToEq m n h)

-- Corollary: succ is injective
theorem Nat.succ_injective' {m n : Nat} (p : m + 1 = n + 1) : m = n :=
  eqNatToEq m n (eqToEqNat (Nat.succ.inj p))

-- Corollary: 0 ≠ succ n
theorem zero_ne_succ' {n : Nat} (p : 0 = n + 1) : False :=
  Empty.elim (eqToEqNat p)


-- ============================================================================
-- Section 11.4: Embeddings
-- ============================================================================

-- Definition 11.4.1: An embedding is a map f such that
-- ap_f : (x = y) → (f(x) = f(y)) is an equivalence for all x, y.

def IsEmb {α : Type u} {β : Type v} (f : α → β) :=
  (x y : α) → IsEquiv (congrArg f : (x = y) → (f x = f y))

def Emb (α : Type u) (β : Type v) := Σ' (f : α → β), IsEmb f

-- Theorem 11.4.2: Any equivalence is an embedding.
def isEmbOfIsEquiv {α : Type u} {β : Type v} (f : α → β)
    (ef : IsEquiv f) : IsEmb f :=
  sorry

-- ============================================================================
-- Section 11.5: Disjointness of coproducts
-- ============================================================================

-- A wrapper to lift Prop into Type u
inductive PropLift.{l} (P : Prop) : Type l where
  | up : P → PropLift P

-- Observational equality on Sum (as Type, not Prop)
def EqSum {α : Type u} {β : Type u} : α ⊕ β → α ⊕ β → Type u
  | .inl x, .inl x' => PropLift (x = x')
  | .inl _, .inr _   => PEmpty
  | .inr _, .inl _   => PEmpty
  | .inr y, .inr y'  => PropLift (y = y')

def reflEqSum {α : Type u} {β : Type u} : (s : α ⊕ β) → EqSum s s
  | .inl _ => PropLift.up rfl
  | .inr _ => PropLift.up rfl

def eqToEqSum {α : Type u} {β : Type u} {s t : α ⊕ β}
    (p : s = t) : EqSum s t :=
  p ▸ reflEqSum s

-- Proposition 11.5.4: Σ(t : α ⊕ β) EqSum(s, t) is contractible.

def isContrTotalEqSumInl {α : Type u} {β : Type u} (x : α)
    : IsContr (Σ (t : α ⊕ β), EqSum (.inl x) t) :=
  ⟨⟨.inl x, PropLift.up rfl⟩, fun ⟨t, e⟩ => by
    cases t with
    | inl x' =>
      cases e with | up h => subst h; rfl
    | inr y' => exact PEmpty.elim e⟩

def isContrTotalEqSumInr {α : Type u} {β : Type u} (y : β)
    : IsContr (Σ (t : α ⊕ β), EqSum (.inr y) t) :=
  ⟨⟨.inr y, PropLift.up rfl⟩, fun ⟨t, e⟩ => by
    cases t with
    | inl x' => exact PEmpty.elim e
    | inr y' =>
      cases e with | up h => subst h; rfl⟩

def isContrTotalEqSum {α : Type u} {β : Type u} (s : α ⊕ β)
    : IsContr (Σ (t : α ⊕ β), EqSum s t) := by
  cases s with
  | inl x => exact isContrTotalEqSumInl x
  | inr y => exact isContrTotalEqSumInr y

-- Theorem 11.5.1: Identity types of coproducts
def isEquivEqToEqSum {α : Type u} {β : Type u} (s : α ⊕ β)
    : ∀ t, IsEquiv (@eqToEqSum _ _ s t) :=
  sorry

-- Corollary: inl and inr are embeddings

def isEmbInl {α : Type u} {β : Type u} : IsEmb (Sum.inl : α → α ⊕ β) :=
  sorry

def isEmbInr {α : Type u} {β : Type u} : IsEmb (Sum.inr : β → α ⊕ β) :=
  sorry


-- ============================================================================
-- Section 11.6: The Structure Identity Principle
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Definition 11.6.1: Dependent identity systems
-- ----------------------------------------------------------------------------

def IsDependentIdentitySystem
    {α : Type u} {a : α}
    {C : α → Type v} {c : C a}
    {B : α → Type u₁}
    (b : B a)
    (D : (x : α) → B x → C x → Type u₂)
    (d : D a b c) :=
  IsIdentitySystem.{u₁, u₂, u₃} b (B := fun y => D a y c) d

-- The combined type family for the SIP
def SIPFamily {α : Type u} {B : α → Type v} {C : α → Type w}
    (D : (x : α) → B x → C x → Type u₁)
    : (Σ x, B x) → Type (max w u₁)
  | ⟨x, y⟩ => Σ z, D x y z

-- Σ-swap: rearranging dependent Σ-types
def sigmaSwap {α : Type u} {B : α → Type v} {C : α → Type w}
    {D : (x : α) → B x → C x → Type u₁}
    : (Σ (t : Σ x, B x), Σ (z : C t.1), D t.1 t.2 z)
    → (Σ (t : Σ x, C x), Σ (y : B t.1), D t.1 y t.2)
  | ⟨⟨x, y⟩, ⟨z, d⟩⟩ => ⟨⟨x, z⟩, ⟨y, d⟩⟩

def sigmaSwapInv {α : Type u} {B : α → Type v} {C : α → Type w}
    {D : (x : α) → B x → C x → Type u₁}
    : (Σ (t : Σ x, C x), Σ (y : B t.1), D t.1 y t.2)
    → (Σ (t : Σ x, B x), Σ (z : C t.1), D t.1 t.2 z)
  | ⟨⟨x, z⟩, ⟨y, d⟩⟩ => ⟨⟨x, y⟩, ⟨z, d⟩⟩

def isEquivSigmaSwap {α : Type u} {B : α → Type v} {C : α → Type w}
    {D : (x : α) → B x → C x → Type u₁}
    : IsEquiv (@sigmaSwap α B C D) :=
  IsEquiv.ofInverse sigmaSwapInv (fun _ => rfl) (fun _ => rfl)

-- (ii) + C identity system → (v)
def structureIdentityPrinciple_ii_to_v
    {α : Type u} {a : α}
    {B : α → Type v} {b : B a}
    {C : α → Type w} {c : C a}
    {D : (x : α) → B x → C x → Type u₁}
    {d : D a b c}
    (hContrC : IsContr (Σ x, C x))
    (hContrBD : IsContr (Σ (y : B a), D a y c))
    : IsContr (Σ (t : Σ x, B x), SIPFamily D t) :=
  sorry

-- The usable form of the SIP via the FTIT
def structureIdentityPrinciple
    {α : Type u} {a : α}
    {B : α → Type v} {b : B a}
    {C : α → Type w} {c : C a}
    {D : (x : α) → B x → C x → Type u₁}
    {d : D a b c}
    (hContrC : IsContr (Σ x, C x))
    (hContrBD : IsContr (Σ (y : B a), D a y c))
    : ∀ (t : Σ x, B x), IsEquiv (fun (p : ⟨a, b⟩ = t) =>
        (p ▸ (⟨c, d⟩ : Σ (z : C a), D a b z) : Σ (z : C t.1), D t.1 t.2 z)) :=
  sorry


-- ============================================================================
-- Example 11.6.3: Identity type of fibers
-- ============================================================================

-- EqFibStructure: characterization of identity types of fibers
-- Given s t : Fib f b, an element of EqFibStructure f s t is
-- a path h : s.1 = t.1 together with a proof that the triangle commutes.
structure EqFibStructure {α : Type u} {β : Type v} (f : α → β) {b : β}
    (s t : Fib f b) : Type u where
  pathFst : s.1 = t.1

def reflEqFibStructure {α : Type u} {β : Type v} (f : α → β) {b : β}
    (s : Fib f b) : EqFibStructure f s s :=
  ⟨rfl⟩

def isContrTotalEqFibStructure
    {α : Type u} {β : Type v} (f : α → β) {b : β}
    (s : Fib f b) : IsContr (Σ (t : Fib f b), EqFibStructure f s t) :=
  sorry

def isEquivEqFibStructure
    {α : Type u} {β : Type v} (f : α → β) {b : β}
    (s t : Fib f b)
    : IsEquiv (fun (p : s = t) =>
        p ▸ reflEqFibStructure f s) :=
  sorry


-- ============================================================================
-- Example: Identity type of pointed types
-- ((A, a) = (B, b)) ≃ Σ(e : A ≃ B) e(a) = b
-- Requires univalence (postulated).
-- ============================================================================

axiom ua {α β : Type u} : (α ≃ β) → (α = β)
axiom uaEquiv {α β : Type u} : IsEquiv (@ua α β)

def PointedType := Σ (α : Type u), α

structure EqPointed (s t : PointedType.{u}) where
  equiv : s.1 ≃ t.1
  ptPath : equiv.toFun s.2 = t.2

-- Σ(B : Type) (A ≃ B) is contractible by univalence
def isContrTotalEquiv {α : Type u}
    : IsContr (Σ (β : Type u), α ≃ β) :=
  sorry

-- Using the SIP:
def eqPointedEquiv (s : PointedType.{u})
    : IsContr (Σ (t : PointedType.{u}), EqPointed s t) :=
  sorry

def isEquivEqPointed (s t : PointedType.{u})
    : IsEquiv (fun (p : s = t) =>
        p ▸ (⟨Equiv.refl s.1, rfl⟩ : EqPointed s s)) :=
  sorry
