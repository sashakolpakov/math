import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChainToCochain
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Map Extend -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MapExtend

noncomputable section

/-! An additive module functor commutes with extending a complex by zero.
This identifies the cochain tensor columns with the original chain-complex
computations used for Tor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] (G : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [G.Additive]
  {I J : Type} {c : ComplexShape I} {c' : ComplexShape J}
  (K : HomologicalComplex (ModuleCat.{0} R) c)

def optionIso (i : Option I) :
    HomologicalComplex.extend.X ((G.mapHomologicalComplex c).obj K) i ≅
      G.obj (HomologicalComplex.extend.X K i) :=
  match i with
  | none => G.mapZeroObject.symm
  | some _ => Iso.refl _

theorem option_comm (i j : Option I) :
    (optionIso R G K i).hom ≫ G.map (HomologicalComplex.extend.d K i j) =
      HomologicalComplex.extend.d ((G.mapHomologicalComplex c).obj K) i j ≫
        (optionIso R G K j).hom := by
  cases i <;> cases j <;>
    simp [optionIso, HomologicalComplex.extend.d]

def iso (e : c.Embedding c') :
    ((G.mapHomologicalComplex c).obj K).extend e ≅
      (G.mapHomologicalComplex c').obj (K.extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => optionIso R G K (e.r i))
    (fun i j _ => option_comm R G K (e.r i) (e.r j))

def cochainIso (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    ChainToCochain.cochain R ((G.mapHomologicalComplex (.down ℕ)).obj K) ≅
      (G.mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R K) :=
  iso R G K (ComplexShape.embeddingUpIntLE 0)

def cochainHomologyIso (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    ((G.mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R K)).homology (-(n : ℤ)) ≅
      ((G.mapHomologicalComplex (.down ℕ)).obj K).homology n :=
  HomologicalComplex.homologyMapIso (cochainIso R G K).symm (-(n : ℤ)) ≪≫
    ChainToCochain.homologyIso R ((G.mapHomologicalComplex (.down ℕ)).obj K) n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MapExtend
