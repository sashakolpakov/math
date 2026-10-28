import OAI.ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

/-! # Closed Identity Section -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection.Abelian.FamilyPoints

noncomputable section

/-!
The identity section of an abelian scheme is a genuine closed immersion.
Its native closed image meets each actual scheme fiber exactly at the
fiber identity. This detects nonperiods without global Hausdorff assumptions
on the total parameter scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)

theorem identitySection_closedImmersion : IsClosedImmersion (AbelianFamilyPoints.FamilyPoints.identitySection S G).left := by
  let : IsSeparated (AbelianFamilyPoints.FamilyPoints.projection S G).left := inferInstanceAs (IsSeparated G.scheme.hom)
  have he : (AbelianFamilyPoints.FamilyPoints.identitySection S G).left ≫ (AbelianFamilyPoints.FamilyPoints.projection S G).left = 𝟙 S.left :=
    congrArg Over.Hom.left (AbelianFamilyPoints.FamilyPoints.identitySection_projection S G)
  let : IsClosedImmersion ((AbelianFamilyPoints.FamilyPoints.identitySection S G).left ≫ (AbelianFamilyPoints.FamilyPoints.projection S G).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp (AbelianFamilyPoints.FamilyPoints.identitySection S G).left (AbelianFamilyPoints.FamilyPoints.projection S G).left

theorem identitySection_native_closed :
    IsClosed (Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.identitySection S G))) := by
  let : IsClosedImmersion (AbelianFamilyPoints.FamilyPoints.identitySection S G).left := identitySection_closedImmersion S G
  exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (AbelianFamilyPoints.FamilyPoints.identitySection S G)).isClosed_range

theorem fiberInclusion_mem_identitySection_iff
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) z ∈
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.identitySection S G)) ↔ z = 1 := by
  constructor
  · rintro ⟨t, ht⟩
    have hbase : t = s :=
      ((AbelianFamilyPoints.FamilyPoints.native_identitySection S G).2 t).symm.trans
        ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.projection S G)) ht).trans
          (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph (AbelianFamilyPoints.FamilyPoints.projection S G) s z).property)
    subst t
    apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)).injective
    exact ht.symm.trans (FiberGroupLaws.Abelian.FamilyPoints.fiberInclusion_one S G s).symm
  · intro hz
    subst z
    exact ⟨s, (FiberGroupLaws.Abelian.FamilyPoints.fiberInclusion_one S G s).symm⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection.Abelian.FamilyPoints
