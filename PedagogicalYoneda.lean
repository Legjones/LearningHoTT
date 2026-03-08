--Categories...

universe u v s

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

--(Covariant) Functors
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
     ext c
     simp only [FA_to_natt, natt_to_FA]
     funext g
     have h := η.Comm g
     simp only [SetCat, Rep_cov] at h
     have h_applied := congrFun h (C.id A)
     simp only [C.id_comp] at h_applied
     exact h_applied.symm


--Below expresses that the composition of the above from FA to FA is the identity
theorem Yoneda_iti_id {C: Cat} (A:C.Obj) {F: Fun C SetCat} (a: F.Fobj A):
  ((natt_to_FA) A) (FA_to_natt A a) = a := by
  simp only [FA_to_natt, natt_to_FA]
  rw [F.Fid]
  simp only [SetCat]


/-We want to express naturality of our above assignments, in A, but to do so
it seems best to introduce some notation for operations on natural transformations
which is what we do here.-/
def f_on_eta {C: Cat} {F: Fun C SetCat} {A B : C.Obj} (f : C.Hom A B) (η: Natt (Rep_cov A) F): Natt (Rep_cov B) F :=
{
  Legs := by
          intro X
          simp only [SetCat, Rep_cov]
          have h := η.Legs X
          simp only [SetCat, Rep_cov] at h
          exact fun g => h (C.comp f g) --Essentially we just precompose with f
  Comm := by
          intro X Y g
          simp only [SetCat, Rep_cov]
          dsimp
          simp only [← C.assoc]
          funext z --The goal is now essentially just naturality of η, precomposing our input z with f
          have e := η.Comm g
          simp only [SetCat, Rep_cov] at e
          have fin := congrFun e (C.comp f z)
          exact fin
}

/-The following expresses naturality in A, with the LHS describing the
"right then down" of the commuting square:
   F(A) → η
F(f) |    | (precomp with f)
     v    v
   F(B) → γ
-/
theorem nat_in_A_FA {C: Cat} {F: Fun C SetCat} {A B :C.Obj} {a : F.Fobj A} (f : C.Hom A B):
   (f_on_eta f) (FA_to_natt A a) = (FA_to_natt B) ((F.Fmor f) a) := by
   ext c
   simp only [FA_to_natt, f_on_eta]
   simp only [F.Fcomp]
   simp only [SetCat]
   rfl


/-The following is expressing that if we have some diagram of the form
· → · → ·
|   |   |
v   v   v
· → · → ·
Where the left square commutes and the outer rectangle commutes and the top
horizontals are isomoprhisms, then the right square commutes. This is one
way to more conceptually approach proving naturality of our other assignment
after we have the previous theorem.

Note also that our explicit assumptions below are just that the outer rectangle
commutes, co, our inner left square commutes, ci, and the reverse composition of our
top two morphisms is the identity, i.e. this pair forms a split epimorphism.-/

theorem two_of_three_squares_hisos {X_1 Y_1 : Type u} {X_2 Y_2 : Type v} (f_1 : X_1 → Y_1) (g_1 : Y_1 → X_1) {f_2 : X_2 → Y_2} {g_2 : Y_2 → X_2} (v_1 : X_1 → X_2) {v_2 : Y_1 → Y_2}
(co :(v_1 ∘ g_1 ∘ f_1) = (g_2 ∘ f_2 ∘  v_1)) (ci : v_2 ∘ f_1 = f_2 ∘ v_1) (id_t : f_1 ∘ g_1 = (fun x =>x)) :
v_1 ∘ g_1 = g_2 ∘ v_2 := by
  funext z
  have l := congrFun co (g_1 z)
  dsimp at l
  have h := congrFun id_t z
  dsimp at h
  rw [h] at l
  have j := congrFun ci (g_1 z)
  dsimp at j
  rw [← j] at l
  have k := congrFun id_t z
  dsimp at k
  rw [k] at l
  exact l


/-In order to apply the above properly we will rephrase the nature of the pieces of the Yoneda theorem
already established, essentially just doing a λ-abstraction to make types all work out. -/


/-Rephrases Yoneda_ntn_id to actually give an equality of function terms so that we can use id_comp_either
applied with congrFun or congrArg, forget which, to get co, our outer commuting diagram. We should be able
do a similar thing for our ci, the lefthand commuting square, and the last piece, id_t, should be exactly
our rephrased Yoneda_iti_id guy.-/


def i A : A → A := fun x => x

theorem id_comp_either {X Y : Type u} (h : X → Y) :
(i Y) ∘ h = h ∘ (i X) := by
rfl

/-The following expresses naturality in A of the assignment in the other direction
to our previous result, using the above lemma. Note that this can be done by hand
using f_on_eta directly, of course.

The way we currently have it does require that we massage things a little bit, rephrasing some
previous results as having assignments/doing some Currying essentially.-/

theorem nat_in_A_nattFA {C: Cat} {F: Fun C SetCat} {A B :C.Obj} (f: C.Hom A B) (η: Natt (Rep_cov A) F) :
 (F.Fmor f) (natt_to_FA A η) = natt_to_FA (B) (f_on_eta f η) := by
  have f_precomp : (Natt (Rep_cov A) F) → (Natt (Rep_cov B) F) := fun γ => f_on_eta f γ
  have co_1 := id_comp_either f_precomp
  have Yon_ntn_top :=
  rw [Yoneda_ntn_id] at co_1
  --have i : (Natt (Rep_cov A) F) → (Natt (Rep_cov A) F) := fun z => (Yoneda_ntn_id A z)
  --have co := congrFun (Yoneda_ntn_id A)
  --have co := congrFun (Yoneda_ntn_id A) (f_on_eta f)
  --have h := two_of_three_squares_hisos.{0,1} (FA_to_natt A) (natt_to_FA A) (f_on_eta f) (congrArg (Yoneda_ntn_id) (f_on_eta f)) (nat_in_A_FA f) (Yoneda_ntn_id A)
