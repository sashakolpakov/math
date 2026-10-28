import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

noncomputable section

/-!
Base change of polarized abelian schemes with full level. Positivity is
transported using actual ample line bundles and actual isomorphisms of the
module sheaves in the normalized Poincare formula.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

/-- Two paths in a commuting square give isomorphic pullbacks of a line bundle. -/
private def pullbackSquareIso {W X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (L : Line.Bundles.LineBundle Z) :
    (Line.Bundles.LineBundle.pullback a (Line.Bundles.LineBundle.pullback b L)).sheaf ≅
      (Line.Bundles.LineBundle.pullback c (Line.Bundles.LineBundle.pullback d L)).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

/-- The positive Poincare formula on a geometric fiber persists under base change. -/
theorem positiveOnGeometricFiber_pullback (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (f : S' ⟶ S)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S')
    (hp : PolarizationData.PositiveOnGeometricFiber D p K (s ≫ f)) :
    PolarizationData.PositiveOnGeometricFiber (D.pullback f) ((Over.pullback f).map p) K s := by
  obtain ⟨L, hL, ⟨eZero⟩, ⟨eFormula⟩⟩ := hp
  let B := ((A.pullback f).pullback s).scheme
  let C := (A.pullback (s ≫ f)).scheme
  let e := A.fiberCompIso f s
  let e₂ := A.fiberProductCompIso f s
  let L' : Line.Bundles.LineBundle B.left := L.pullback e.hom
  refine ⟨L', hL.pullback_of_isIso e.hom, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp η[B].left e.hom).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (A.fiberCompIso_hom_one f s)).app L.sheaf ≪≫ eZero
  · let Q₀ := (PolarizationData.polarizationBiextensionAt D p (s ≫ f)).sheaf
    let Q₁ := (L.pullback (fst C C).left).sheaf
    let Q₂ := (L.pullback (snd C C).left).sheaf
    let e₀ := FiberComparison.polarizationBiextensionCompIso D p f s
    let e₁ : (L'.pullback (fst B B).left).sheaf ≅
        (Scheme.Modules.pullback e₂.hom).obj Q₁ :=
      pullbackSquareIso (fst B B).left e.hom e₂.hom (fst C C).left
        (A.fiberProductCompIso_hom_fst f s).symm L
    let e₃ : (L'.pullback (snd B B).left).sheaf ≅
        (Scheme.Modules.pullback e₂.hom).obj Q₂ :=
      pullbackSquareIso (snd B B).left e.hom e₂.hom (snd C C).left
        (A.fiberProductCompIso_hom_snd f s).symm L
    exact Tensor.ProductSheaf.tensorModuleCongr
        (Tensor.ProductSheaf.tensorModuleCongr e₀ e₁ ≪≫ (Tensor.ProductBaseChange.tensorModulePullbackIso e₂.hom Q₀ Q₁).symm) e₃ ≪≫
      (Tensor.ProductBaseChange.tensorModulePullbackIso e₂.hom (Tensor.ProductSheaf.tensorModule Q₀ Q₁) Q₂).symm ≪≫
      (Scheme.Modules.pullback e₂.hom).mapIso eFormula ≪≫
      pullbackSquareIso e₂.hom μ[C].left μ[B].left e.hom
        (A.fiberProductCompIso_hom_mul f s) L

/-- Base change of a polarization preserves its finite flat isogeny, type,
and positivity on every geometric fiber. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.Polarization.pullback {D : Dual.Data.DualAbelianData A} {δ : Fin g → ℕ}
    (p : PolarizationData.Polarization D δ) (f : S' ⟶ S) : PolarizationData.Polarization (D.pullback f) δ where
  isogeny := p.isogeny.pullback f
  kernelType := p.kernelType.pullback f
  positive K _ _ s := positiveOnGeometricFiber_pullback D p.isogeny.hom f K s (p.positive K (s ≫ f))

/-- Pullback of all the data in the polarized full-level moduli problem. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback {δ : Fin g → ℕ} {N : ℕ}
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : S' ⟶ S) :
    PolarizationData.PolarizedAbelianWithFullLevel g δ N S' where
  abelian := B.abelian.pullback f
  dual := B.dual.pullback f
  polarization := B.polarization.pullback f
  level := B.level.pullback f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
