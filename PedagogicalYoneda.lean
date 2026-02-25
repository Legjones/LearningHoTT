--Categories...

universe u v

structure Cat where
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
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
  (Fid : ∀ {X : C.Obj}, Fmor (C.id X) = D.id (Fobj X)) --Compatibility with identity

--Composition of functors (is a functor)
def FunComp {C D E : Cat} (G : Fun D E) (F : Fun C D): Fun C E:=
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
@[ext]
structure Natt (F G : Fun C D) where
  (Legs : ∀ (X: C.Obj), D.Hom (F.Fobj X) (G.Fobj X)) --Legs of the natural transformation
  (Comm : ∀ {X Y : C.Obj} (f: C.Hom X Y), D.comp (F.Fmor f) (Legs Y) = D.comp (Legs X) (G.Fmor f)) --The necessary commuting diagrams


--The identity natural transformation for a given functor
def idNatt {C D : Cat} (F: Fun C D) : Natt F F :=
{
  Legs := fun X => D.id (F.Fobj X),
  Comm := by
          intro X Y F
          rw [D.comp_id]
          rw [D.id_comp]
}

--A model for the category of (small) sets (hopefully...)
def SetCat : Cat :=
{
  Obj := Type,
  Hom := fun X Y => X → Y,
  id  := fun X x => x,
  comp := fun f g x => g (f x),
  id_comp := by intros; rfl,
  comp_id := by intros; rfl,
  assoc := by intros; rfl
}

--Covariant representable functors (i.e. representable in the first coordinate)
@[simp]
def Rep_cov {C: Cat} : C.Obj → Fun C SetCat :=
  fun A : C.Obj =>
  {
    Fobj:= fun X: C.Obj => C.Hom A X,
    Fmor:= fun {X Y : C.Obj} (f : C.Hom X Y) (g : C.Hom A X) => C.comp g f
    Fcomp := by
          intros
          simp only [SetCat, C.assoc]
    Fid := by
          intros
          simp only [SetCat, C.comp_id]
  }


--The construction of a natrual transformation from an element of F(A)
def FA_to_natt {C: Cat} {F: Fun C SetCat}: (A : C.Obj) → (F.Fobj A) →  Natt (Rep_cov A) F :=
  fun A : C.Obj => (fun (z : F.Fobj A) =>
  {
    Legs := fun X => (fun (g : (Rep_cov A).Fobj X) => (F.Fmor g) z),
    Comm := by
            intro X Y f
            simp only [SetCat, Rep_cov, F.Fcomp]
  })

--The construction of an element of F(A) from a natural transformation
def natt_to_FA {C: Cat} {F: Fun C SetCat}: (A: C.Obj) → Natt (Rep_cov A) F → (F.Fobj A) :=
  fun A: C.Obj =>
    (fun (η : Natt (Rep_cov A) F) =>  (η.Legs A) (C.id A))

/-The above works... but feels a bit hacky, since I am seemingly depending on the
unwrapping of things at the end step, and under the hood. I mean this specifically
for the situation of the typing for identifying ((Rep_cov A).Fobj A) with (C.Hom A A).-/

--Below expresses that the composition of the above from natt to natt is the identity
theorem Yoneda_ntn_id {C: Cat} (A: C.Obj) {F: Fun C SetCat} (η : Natt (Rep_cov A) F) :
  (FA_to_natt A) ((natt_to_FA A) η) = η := by
     ext
     apply funext
     simp only [FA_to_natt, natt_to_FA]
     simp [η.Comm] --I feel like I'm going a bit crazy, because this is definitely
     --the kind of thing I want to do (just use the fact that F(x) ∘ η_A(id_A) =
     -- η_{cod(x)} ∘ (Rep_cov A) (id_A) = η_{cod(x)} ∘ id_A = η_{cod(x)}, in the first
     -- part just expressing the naturality square). I've tried doing this a number of
     -- different ways but all have failed...
