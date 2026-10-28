import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Polarization Line Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationLineSymmetry.Construction

noncomputable section

/-!
The original polarization line formula forces symmetry of its actual
biextension line. Tensor cancellation takes place in the proved Picard
group of genuine line bundles; the resulting symmetry is an actual
isomorphism of module sheaves, not a symmetry assumption on the pairing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction

universe u

theorem lineClass_symmetry_of_polarization_formula
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule P.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A A).hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P := by
  let c := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P
  let a := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst A A).left)
  let b := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd A A).left)
  let m := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback μ[A].left)
  let σ := Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (β_ A A).hom.left
  have hm : c * a * b = m := Quotient.sound hformula
  have ha : σ a = b := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A A).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (congrArg Over.Hom.left (braiding_hom_fst A A))
  have hb : σ b = a := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A A).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (congrArg Over.Hom.left (braiding_hom_snd A A))
  have hμ : σ m = m := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A A).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (congrArg Over.Hom.left (IsCommMonObj.mul_comm A))
  have hs := congrArg σ hm
  rw [map_mul, map_mul, ha, hb, hμ] at hs
  have hs' : σ c * a * b = m := by
    calc
      σ c * a * b = σ c * b * a := by ac_rfl
      _ = m := hs
  exact mul_right_cancel (mul_right_cancel (hs'.trans hm.symm))

def lineSymmetryOfPolarizationFormula
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule P.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf)) :
    (Scheme.Modules.pullback (β_ A A).hom.left).obj P.sheaf ≅ P.sheaf :=
  Classical.choice (Quotient.exact (lineClass_symmetry_of_polarization_formula A P L hformula))

theorem geometricPolarizationBiextension_has_symmetry
    {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    Nonempty ((Scheme.Modules.pullback
      (β_ (A.pullback s).scheme (A.pullback s).scheme).hom.left).obj
      (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D pol.isogeny.hom s).sheaf ≅
        (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D pol.isogeny.hom s).sheaf) := by
  obtain ⟨L, _, _, hformula⟩ := pol.positive k s
  exact ⟨lineSymmetryOfPolarizationFormula (A.pullback s).scheme
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D pol.isogeny.hom s) L hformula⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationLineSymmetry.Construction
