def hello := "world"

inductive Color : Type
| red
| green
| blue

def favorite_color : Color := Color.blue

def color_change : Color → Color
| Color.red   => Color.green
| Color.green => Color.blue
| Color.blue  => Color.red

#check color_change
#eval color_change Color.red

#eval 34 + 8

def color_fam : Color → Type
| Color.red   => Unit
| Color.green => Bool
| Color.blue  => Nat

def color_dep_func (c : Color) : color_fam c :=
  match c with
  | Color.red   => ()
  | Color.green => true
  | Color.blue  => Nat.zero



axiom Ob : Type
axiom Mor : Ob → Ob → Type
axiom uni : (A : Ob) → Mor A A
axiom comp {A B C : Ob} : Mor A B → Mor B C → Mor A C
