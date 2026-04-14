/-
  Chapter 10: Contractible types, fibers, and the equivalence characterization
  From: Introduction to Homotopy Type Theory, Egbert Rijke
  -------------------------------------------------------
  Lean 4 implementation — M782, Lecture 8.

  Under Lean's UIP, path algebra, coherent invertibility, and naturality
  of homotopies are all trivial. We focus on:
    - Contractible types (10.1)
    - Singleton induction (10.2)
    - Fibers of maps (10.3)
    - Contractible maps and the equivalence characterization (10.4)
    - Closure properties of contractible types
-/

universe u v w

-- ============================================================================
-- Imports from lecture 7
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

-- Definition 10.1.1: is-contr(A) := Σ(c : A) Π(x : A) c = x
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
-- `PLift` wraps a `Prop` into `Type` so it can be used in `Sigma`.

def isContrTotalPath {α : Type u} (a : α) : IsContr (Σ x, PLift (a = x)) :=
  ⟨⟨a, PLift.up rfl⟩, fun ⟨x, ⟨p⟩⟩ => by subst p; rfl⟩


-- ============================================================================
-- Section 10.2: Singleton induction
-- ============================================================================

-- ev-pt : evaluation at a point
def evPt {α : Type u} (a : α) {B : α → Sort v} (f : (x : α) → B x) : B a := f a

-- is-singleton(a) := ∀ B, sec(evPt a)
-- A pointed type (A, a) satisfies singleton induction if evPt a has a
-- section for every family B.
def IsSingleton.{u₁, u₂} {α : Type u₁} (a : α) :=
  (B : α → Type u₂) → Section (evPt a (B := B))

-- Direction ⇒: Contractible implies singleton induction
def contrToSingleton.{u₁, u₂} {α : Type u₁} {a : α}
    (h : IsContr α) : IsSingleton.{u₁, u₂} a := by
  intro B
  let C := h.contraction
  have C' : (x : α) → a = x := fun x => (C a).symm.trans (C x)
  exact ⟨
    fun b x => C' x ▸ b,
    fun b => rfl
    ⟩

-- Direction ⇐: Singleton induction implies contractible
-- We apply singleton induction to B(x) := PLift (a = x).
def singletonToContr {α : Type u} {a : α}
    (sing : IsSingleton.{u, 0} a) : IsContr α := by
  let B := fun x:α => PLift (a=x)
  let c := (sing B).inv (PLift.up rfl)
  exact ⟨a , fun x => (c x).down⟩
  --The above is not mine



-- ============================================================================
-- Section 10.3: Fibers of maps
-- ============================================================================

-- fib_f(b) := Σ'(a : A) f(a) = b
-- We use PSigma because `f a = b` is `Prop`.
def Fib {α : Type u} {β : Type v} (f : α → β) (b : β) := PSigma (fun a => f a = b)

-- Under UIP, two fiber elements are equal iff their base points are equal.
theorem fib_eq {α : Type u} {β : Type v} {f : α → β} {b : β} {s t : Fib f b}
    (h : s.1 = t.1) : s = t := by
  cases s with | mk a p => cases t with | mk a' q => simp at h; subst h; rfl


-- ============================================================================
-- Section 10.4: Contractible maps
-- ============================================================================

-- A map is contractible if all fibers are contractible (Voevodsky's definition).
def IsContrMap {α : Type u} {β : Type v} (f : α → β) := ∀ b, IsContr (Fib f b)

-- Theorem: Any contractible map is an equivalence
def isEquivOfContrMap {α : Type u} {β : Type v} {f : α → β}
    (cf : IsContrMap f) : IsEquiv f :=
  IsEquiv.ofInverse
    sorry
    sorry
    sorry


-- ============================================================================
-- Section 10.5: Coherently invertible maps
-- ============================================================================
-- Under UIP, coherent invertibility reduces to plain invertibility.

structure HasInverse (f : α → β) where
  inv  : β → α
  rinv : ∀ b, f (inv b) = b
  linv : ∀ a, inv (f a) = a

-- Under UIP, the coherence is trivially satisfied.
structure IsCohInvertible (f : α → β) extends HasInverse f where
  coherence : ∀ a, rinv (f a) = congrArg f (linv a)

def IsEquiv.ofHasInverse {f : α → β} (h : HasInverse f) : IsEquiv f :=
  IsEquiv.ofInverse h.inv h.rinv h.linv

-- is-equiv → has-inverse: show the section inverse also works as retraction inverse.
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

-- Step 3 of the chain: is-coh-invertible → is-contr-map
-- Given (g, G, H, K) : is-coh-invertible f, the center of fib_f(y) is (g y, G y).
-- For any (x, refl) : fib_f(f x), we need (g(fx), G(fx)) = (x, refl).
-- We use Eq-fib: take α := H(x) : g(fx) = x, then the coherence K gives
-- G(fx) = ap_f(H(x)), which (after adjusting for refl) closes the goal.
-- Under UIP, the coherence is automatic.
def isContrMapOfCohInvertible {α : Type u} {β : Type v} {f : α → β}
    (ci : IsCohInvertible f) : IsContrMap f :=
  sorry

-- The full chain: is-equiv → has-inverse → is-coh-invertible → is-contr-map
def isContrMapOfIsEquiv {α : Type u} {β : Type v} {f : α → β}
    (e : IsEquiv f) : IsContrMap f :=
  isContrMapOfCohInvertible (IsCohInvertible.ofIsEquiv e)

-- Corollary via the main theorem
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

-- Retracts of contractible types are contractible
structure IsRetractOf (α : Type u) (β : Type v) where
  section_ : α → β
  retract  : β → α
  isRetr   : ∀ a, retract (section_ a) = a

def isContrRetractOf {α : Type u} {β : Type v}
    (r : IsRetractOf α β) (hB : IsContr β) : IsContr α :=
  sorry

-- Contractible types are closed under equivalences
def isContrOfEquiv {α : Type u} {β : Type v}
    (f : α → β) (e : IsEquiv f) (hB : IsContr β) : IsContr α :=
  isContrRetractOf ⟨f, e.retr.inv, e.retr.leftInv⟩ hB

def isContrOfEquiv' {α : Type u} {β : Type v}
    (f : α → β) (e : IsEquiv f) (hA : IsContr α) : IsContr β :=
  isContrRetractOf ⟨e.sec.inv, f, e.sec.rightInv⟩ hA

-- Any map between contractible types is an equivalence
def isEquivOfIsContr {α : Type u} {β : Type v}
    (f : α → β) (hA : IsContr α) (hB : IsContr β) : IsEquiv f :=
  sorry

def equivOfIsContr {α : Type u} {β : Type v}
    (hA : IsContr α) (hB : IsContr β) : α ≃ β :=
  sorry

-- Contractibility of Σ-types
def isContrSigma {α : Type u} {B : α → Type v}
    (hA : IsContr α) (hB : IsContr (B hA.center)) : IsContr (Σ x, B x) :=
  sorry

def isContrSigma' {α : Type u} {B : α → Type v}
    (hA : IsContr α) (hB : ∀ x, IsContr (B x)) : IsContr (Σ x, B x) :=
  isContrSigma hA (hB hA.center)

-- Contractible types are propositions
def isPropIsContr {α : Type u} (h : IsContr α) (x y : α)
    : IsContr (PLift (x = y)) :=
  ⟨PLift.up (eq_of_isContr h), fun ⟨_⟩ => rfl⟩

-- Products of families of contractible types are contractible
def isContrPi {α : Type u} {B : α → Type v}
    (hB : ∀ x, IsContr (B x)) : IsContr ((x : α) → B x) :=
  sorry

def isContrFunctionType {α : Type u} {β : Type v}
    (hB : IsContr β) : IsContr (α → β) :=
  isContrPi (fun _ => hB)

-- Being contractible is itself contractible (when it holds)
def isContrIsContr {α : Type u} (h : IsContr α) : IsContr (IsContr α) :=
  sorry

theorem isPropIsContr' {α : Type u} (h k : IsContr α) : h = k :=
  sorry
