import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison

/-! # Cochain Prescribed Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CochainPrescribedLift.Constructions

noncomputable section

/-! Lift a cochain through an actual cohomology equivalence while preserving its prescribed differential. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem cochainClass_succ_eq_zero_iff (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C (n+1)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass C (n+1) u = 0 ↔ ∃ v : C.X n, C.d n (n+1) v = u.val := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff]
  change (∃ v : (C.sc (n+1)).X₁, AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap C (n+1) v = u) ↔ _
  constructor
  · rintro ⟨v,hv⟩
    exact (BinarySmallRightCup.Constructions.cochainBoundary_succ_iff C n u.val).mp ⟨v,congrArg Subtype.val hv⟩
  · intro hv
    obtain ⟨v,hv⟩ := (BinarySmallRightCup.Constructions.cochainBoundary_succ_iff C n u.val).mpr hv
    exact ⟨v,Subtype.ext hv⟩

theorem cochain_prescribed_lift {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ}
    (e : C ⟶ D) (n : ℕ)
    (he : Function.Surjective (HomologicalComplex.homologyMap e n))
    (he' : Function.Injective (HomologicalComplex.homologyMap e (n+1)))
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C (n+1)) (w : D.X n)
    (hw : D.d n (n+1) w = e.f (n+1) u.val) :
    ∃ (v : C.X n) (z : (D.sc n).X₁),
      C.d n (n+1) v = u.val ∧ (D.sc n).f z = e.f n v - w := by
  have hu0 : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass C (n+1) u = 0 := by
    apply he'
    rw [map_zero, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
    exact (cochainClass_succ_eq_zero_iff D n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap e (n+1) u)).mpr ⟨w,hw⟩
  obtain ⟨v₀,hv₀⟩ := (cochainClass_succ_eq_zero_iff C n u).mp hu0
  have hz : e.f n v₀ - w ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D n := by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, map_sub]
    have h := ConcreteCategory.congr_hom (e.comm n (n+1)) v₀
    change D.d n (n+1) (e.f n v₀) = e.f (n+1) (C.d n (n+1) v₀) at h
    rw [h, hv₀, hw, sub_self]
  let a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D n := ⟨e.f n v₀ - w,hz⟩
  obtain ⟨t,ht⟩ := he (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass D n a)
  obtain ⟨t,ht'⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective C n t
  rw [← ht', AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality] at ht
  obtain ⟨z,hz⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists D n a (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap e n t)).mp ht.symm
  refine ⟨v₀-t.val,z,?_,?_⟩
  · rw [map_sub, hv₀, AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ t, sub_zero]
  · rw [map_sub]
    change (D.sc n).f z = e.f n v₀ - e.f n t.val - w
    change (D.sc n).f z = (e.f n v₀ - w) - e.f n t.val at hz
    rw [hz]
    abel

theorem binarySmallRelative_prescribed_lift (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n+1))
    (w : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X n)
    (hw : (BinarySmallCochains.Constructions.binarySmallCochains X A B).d n (n+1) w =
      (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f (n+1) u.val) :
    ∃ (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).X n)
      (z : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc n).X₁),
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).d n (n+1) v = u.val ∧
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc n).f z =
        (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f n v - w :=
  cochain_prescribed_lift (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) n
    (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective X A B hA hB n).surjective
    (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective X A B hA hB (n+1)).injective u w hw

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CochainPrescribedLift.Constructions
