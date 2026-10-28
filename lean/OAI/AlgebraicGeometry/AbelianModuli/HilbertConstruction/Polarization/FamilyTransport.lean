import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyTransport

noncomputable section

/-! Transport polarizations through an isomorphism of abelian families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

private def familyPullbackSquareIso {W X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (L : Line.Bundles.LineBundle Z) :
    (Line.Bundles.LineBundle.pullback a (Line.Bundles.LineBundle.pullback b L)).sheaf ≅
      (Line.Bundles.LineBundle.pullback c (Line.Bundles.LineBundle.pullback d L)).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

/-- The ample line bundle inducing a geometric polarization pulls back through
the fiber isomorphism and still satisfies the normalized Poincare formula. -/
theorem positiveOnGeometricFiber_familyTransport (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (hp : PolarizationData.PositiveOnGeometricFiber D p K s) :
    PolarizationData.PositiveOnGeometricFiber (D.familyTransport e) (e.inv ≫ p) K s := by
  obtain ⟨L, hL, ⟨eZero⟩, ⟨eFormula⟩⟩ := hp
  let X := (B.pullback s).scheme
  let Y := (A.pullback s).scheme
  let a : X ⟶ Y := (Over.pullback s).map e.inv
  let a₂ : X ⊗ X ⟶ Y ⊗ Y := a ⊗ₘ a
  have : IsIso a := inferInstanceAs (IsIso ((Over.pullback s).map e.inv))
  have : IsIso a.left := inferInstanceAs (IsIso ((Over.forget _).map a))
  have : IsIso a₂ := inferInstanceAs (IsIso (a ⊗ₘ a))
  have : IsIso a₂.left := inferInstanceAs (IsIso ((Over.forget _).map a₂))
  have : IsMonHom a := inferInstanceAs (IsMonHom ((Over.pullback s).map e.inv))
  let L' : Line.Bundles.LineBundle X.left := L.pullback a.left
  refine ⟨L', hL.pullback_of_isIso a.left, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp η[X].left a.left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr
        (congrArg Over.Hom.left (IsMonHom.one_hom a))).app L.sheaf ≪≫ eZero
  · let Q₀ := (PolarizationData.polarizationBiextensionAt D p s).sheaf
    let Q₁ := (L.pullback (fst Y Y).left).sheaf
    let Q₂ := (L.pullback (snd Y Y).left).sheaf
    let e₀ := FamilyComparison.polarizationBiextensionFamilyIso D p e s
    let e₁ : (L'.pullback (fst X X).left).sheaf ≅
        (Scheme.Modules.pullback a₂.left).obj Q₁ :=
      familyPullbackSquareIso (fst X X).left a.left a₂.left (fst Y Y).left
        (Over.tensorHom_left_fst _ _ _ _).symm L
    let e₂ : (L'.pullback (snd X X).left).sheaf ≅
        (Scheme.Modules.pullback a₂.left).obj Q₂ :=
      familyPullbackSquareIso (snd X X).left a.left a₂.left (snd Y Y).left
        (Over.tensorHom_left_snd _ _ _ _).symm L
    exact Tensor.ProductSheaf.tensorModuleCongr
        (Tensor.ProductSheaf.tensorModuleCongr e₀ e₁ ≪≫ (Tensor.ProductBaseChange.tensorModulePullbackIso a₂.left Q₀ Q₁).symm) e₂ ≪≫
      (Tensor.ProductBaseChange.tensorModulePullbackIso a₂.left (Tensor.ProductSheaf.tensorModule Q₀ Q₁) Q₂).symm ≪≫
      (Scheme.Modules.pullback a₂.left).mapIso eFormula ≪≫
      familyPullbackSquareIso a₂.left μ[Y].left μ[X].left a.left
        (congrArg Over.Hom.left (IsMonHom.mul_hom a)).symm L

/-- A polarization retains its type and positivity after family transport. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.Polarization.familyTransport {D : Dual.Data.DualAbelianData A} {δ : Fin g → ℕ}
    (p : PolarizationData.Polarization D δ) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    PolarizationData.Polarization (D.familyTransport e) δ where
  isogeny := p.isogeny.familyTransport e
  kernelType := p.kernelType.familyTransport e
  positive K _ _ s :=
    positiveOnGeometricFiber_familyTransport D p.isogeny.hom e K s (p.positive K s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyTransport
