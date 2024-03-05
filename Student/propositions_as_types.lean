/-!Torsor over transfromation -/
/-!Proposition is either t or f-/

inductive BobStudiesAtUVA
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVA
| attendsClasses
| paidTuition

inductive MarcoStudiesAtUVA

def neg (α :Type) := α → Empty

example: neg MarcoStudiesAtUVA :=
λ m: MarcoStudiesAtUVA => nomatch m


inductive BobStudiesAtUVAAndMaryStudiesAtUVA
| foo (b: BobStudiesAtUVA) (m: MaryStudiesAtUVA)

def b : BobStudiesAtUVA := BobStudiesAtUVA.paidTuition
def m : MaryStudiesAtUVA := MaryStudiesAtUVA.paidTuition
example : BobStudiesAtUVAAndMaryStudiesAtUVA :=
  BobStudiesAtUVAAndMaryStudiesAtUVA.foo b m


inductive BobStudiesAtUVAOrMaryStudiesAtUVA
| left (b:BobStudiesAtUVA)
| right (m: MaryStudiesAtUVA)

example : BobStudiesAtUVAOrMaryStudiesAtUVA :=
  BobStudiesAtUVAOrMaryStudiesAtUVA.left b
