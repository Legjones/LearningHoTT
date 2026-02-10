--Categories...
/-TODO: Redo the following definition of cat so that we actually worry about universes...
Seem to need to do something like this to talk about our example of Set, even just to talk
about the Yoneda lemma...-/
structure Cat where
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  (id  : ∀ X, Hom X X)
  (comp : ∀ {X Y Z}, Hom X Y → Hom Y Z → Hom X Z)
  (id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f)
  (comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f)
  (assoc : ∀ {W X Y Z}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h))

--Domain and codomain...
def dom : (C : Cat) →  (X Y : C.Obj) → (f : C.Hom X Y) → C.Obj :=  fun _ X _ _ => X

def cod : (C: Cat) → (X Y : C.Obj) → (f: C.Hom X Y) → C.Obj := fun _ _ Y _ => Y

--(Covariant) Functors...
structure Fun (C D :Cat) where
  (Fobj : C.Obj → D.Obj)
  (Fmor : ∀ {X Y: C.Obj}, C.Hom X Y → D.Hom (Fobj X) (Fobj Y))
  (Fcomp : ∀ {X Y Z : C.Obj} (g: C.Hom X Y) (f: C.Hom Y Z), Fmor (C.comp g f) = D.comp (Fmor g) (Fmor f)) --Compatibility with composition
  (Fid : ∀ {X : C.Obj}, Fmor (C.id X) = D.id (Fobj X))

--Composition of functors (is a functor)
def FunComp (C D E : Cat) (G : Fun D E) (F : Fun C D): Fun C E:=
  {
    Fobj := fun c => G.Fobj (F.Fobj c)
    Fmor := fun f => G.Fmor (F.Fmor f)
    Fcomp := by
          intro X Y Z g f
          rw [F.Fcomp]
          rw [G.Fcomp]
    Fid := by
          intro X
          rw [F.Fid]
          rw [G.Fid]
  }

--Natural transformations
structure Natt (F G : Fun C D) where
  (Legs : ∀ {X: C.Obj}, D.Hom (F.Fobj X) (G.Fobj X))
  (Comm : ∀ {X Y : C.Obj} (f: C.Hom X Y), D.comp (F.Fmor f) (Legs) = D.comp (Legs) (G.Fmor f))

universe u

--A model for the category of (small) sets (hopefully...)
def SetCat : Cat :=
{ Obj := Type,
  Hom := fun X Y => X → Y,
  id  := fun X x => x,
  comp := fun f g x => g (f x),
  id_comp := by intros; rfl,
  comp_id := by intros; rfl,
  assoc := by intros; rfl }

def Rep_cov {C : Cat} (A: C.Obj) : Fun C SetCat:=
  {

  }
