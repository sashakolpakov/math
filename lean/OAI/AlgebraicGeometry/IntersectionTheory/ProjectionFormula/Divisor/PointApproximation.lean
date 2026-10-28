import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedPrincipalOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.AffineFactorial
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Approximation

/-! # Point Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointApproximation

noncomputable section

/-! A principal divisor can agree with any specified prime divisor
along every divisor through finitely many chosen points in every smooth dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem exists_equation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (S : Finset X.carrier) (A : X.DimensionCycleSupport 1) :
    ∃ g : X.carrier.functionField, g ≠ 0 ∧
      ∀ C ∈ S, ∀ B : X.DimensionCycleSupport 1, C ∈ (B.val : Set X.carrier) →
        X.carrier.ord g (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = if B = A then 1 else 0 := by
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    obtain ⟨U, hU, hmem⟩ := Projective.AffineNeighborhood.common_affine X.projective
      (fun i : Option S => i.elim (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (fun C => C.val))
    let : Nonempty U := ⟨⟨CycleClass.Thom.IntersectionGeometry.supportPoint A.val, hmem none⟩⟩
    let R := Γ(X.carrier, U)
    let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let P : S → PrimeSpectrum R := fun C => hU.primeIdealOf ⟨C.val, hmem (some C)⟩
    let p : PrimeSpectrum R := hU.primeIdealOf ⟨CycleClass.Thom.IntersectionGeometry.supportPoint A.val, hmem none⟩
    have hP (C : S) : hU.fromSpec (P C) = C.val := hU.fromSpec_primeIdealOf _
    have hp : hU.fromSpec p = CycleClass.Thom.IntersectionGeometry.supportPoint A.val := hU.fromSpec_primeIdealOf _
    have hpheight : p.asIdeal.height = 1 := by
      rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec, hp]
      exact CurveSupports.coheight_one X m A
    have hprincipal (C : S) :
        (p.asIdeal.map (algebraMap R (Localization.AtPrime (P C).asIdeal))).IsPrincipal :=
      Smooth.AffineFactorial.height_one_principal X m U hU
        ⟨C.val, hmem (some C)⟩
        p hpheight
    obtain ⟨r, hr, he⟩ := LocalizedPrincipalOrder.exists_orders R P p hpheight hprincipal
    let a : (Spec (.of R)).functionField := StructureSheaf.toStalk R (genericPoint (Spec (.of R))) r
    have ha : a ≠ 0 := by
      change algebraMap R (Spec (.of R)).functionField r ≠ 0
      exact (map_ne_zero_iff _ (IsFractionRing.injective R (Spec (.of R)).functionField)).mpr hr
    let g := (DivisorRestriction.openFieldIso hU.fromSpec).inv a
    have hga : DivisorRestriction.openFieldMap hU.fromSpec g = a :=
      ConcreteCategory.congr_hom (DivisorRestriction.openFieldIso hU.fromSpec).inv_hom_id a
    refine ⟨g, ?_, fun C hC B hCB => ?_⟩
    · intro hg
      apply ha
      rw [← hga, hg, map_zero]
    · let C' : S := ⟨C, hC⟩
      have hspec : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ⤳ C :=
        (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).specializes
          hCB
      have hBU : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ U := hspec.mem_open U.isOpen (hmem (some C'))
      let q : PrimeSpectrum R := hU.primeIdealOf ⟨CycleClass.Thom.IntersectionGeometry.supportPoint B.val, hBU⟩
      have hq : hU.fromSpec q = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := hU.fromSpec_primeIdealOf _
      have hqheight : q.asIdeal.height = 1 := by
        rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec, hq]
        exact CurveSupports.coheight_one X m B
      have hle : q ≤ P C' := by
        apply (PrimeSpectrum.le_iff_specializes _ _).mpr
        apply hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
        rw [hq, hP]
        exact hspec
      have hiff : q = p ↔ B = A := by
        constructor
        · intro h
          apply Subtype.ext
          apply irreducibleSetEquivPoints.injective
          exact hq.symm.trans ((congrArg hU.fromSpec h).trans hp)
        · intro h
          apply hU.fromSpec.isEmbedding.injective
          rw [hq, hp, h]
      rw [← hq, ← DivisorRestriction.ord_openImmersion hU.fromSpec, hga]
      exact (he C' q hqheight hle).trans (by simp only [hiff])
  · refine ⟨1, one_ne_zero, fun C hC => ?_⟩
    exact (hS ⟨C, hC⟩).elim

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointApproximation
