import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationPELIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsoPreimages
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingFiberFamily
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTargetDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame

/-! # Central Geometric Targets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central geometric target is the actual q-scalar marking
change. Its comparison is constructed from multiplication by q and
then identified using the full actual Tate preimage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry)

section Fiber
variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.qMarkingFiberIsogeny :
    PELIsogenies.PELIsogeny (D.fiberFamily b x)
      (D.fiberFamily b (x ≫ (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom)) (q ^ 2) :=
  (((D.fiberFamily b x).multiplicationPELIsogeny q hg.2.2.1).comp
    (D.markingFiberFamilyIso hgeometry b x (ZMod.unitOfCoprime q hg.2.2.1)).symm.toIsogeny).castMultiplier
      (Nat.mul_one (q ^ 2))

theorem Data.SphericalPELAlbaneseData.qMarkingFiberIsogeny_hom :
    (D.qMarkingFiberIsogeny hg hgeometry b x).isogeny.hom =
      ((𝟙 (D.fiberFamily b x).abelian.scheme) ^ q) ≫
        (D.markingFiberFamilyIso hgeometry b x (ZMod.unitOfCoprime q hg.2.2.1)).abelian.inv := by
  exact PELIsogenies.PELIsogeny.castMultiplier_hom (Nat.mul_one (q ^ 2)) _

theorem Data.SphericalPELAlbaneseData.qMarkingFiberIsogeny_preimage :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (D.qMarkingFiberIsogeny hg hgeometry b x).isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        ((𝟙 (D.fiberFamily b x).abelian.scheme) ^ q) := by
  have : IsMonHom
      (D.markingFiberFamilyIso hgeometry b x (ZMod.unitOfCoprime q hg.2.2.1)).abelian.symm.hom :=
    (D.markingFiberFamilyIso hgeometry b x (ZMod.unitOfCoprime q hg.2.2.1)).symm.abelianGroup
  simp only [D.qMarkingFiberIsogeny_hom]
  exact IsoPreimages.isogenyTatePreimage_comp_iso _ q _
    (D.markingFiberFamilyIso hgeometry b x (ZMod.unitOfCoprime q hg.2.2.1)).abelian.symm

end Fiber

variable (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralEndpoint_eq_marking {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
    (c : (D.correspondence (Local.IntegralType.central s)).Fiber x) :
    c.val ≫ (D.correspondence (Local.IntegralType.central s)).target =
      x ≫ (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom := by
  have := FiberLattices.charZero_of_field_spec_map b
  let frame := D.geometricSplitFrame hg hdegree hs hgeometry b x
  have hf := D.geometricSplitFrame_equivariant hg hdegree hs hgeometry b x
  apply D.geometricTarget_eq_of_preimage_eq hg hgeometry x _ _
    (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x _ c.val c.property rfl)
    (D.qMarkingFiberIsogeny hg hgeometry b x)
  rw [D.qMarkingFiberIsogeny_preimage]
  exact D.centralTatePreimage_eq_multiplication hg hgeometry hIsogenyQuotient hElementaryDivisors b x frame hf c

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
