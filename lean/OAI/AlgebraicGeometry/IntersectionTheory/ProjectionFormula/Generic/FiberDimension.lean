import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DivisorDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ImageDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveLocalRings

/-! # Fiber Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberDimension

noncomputable section

/-! The points above the generic point in a relative curve have height
at most one. A divisor with nonzero pushforward degree lies above that
generic point. All comparisons use the actual affine chart maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (g : Y ⟶ Spec (.of K))
  [LocallyOfFiniteType g] [LocallyOfFiniteType (f ≫ g)]
  (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g))

include g hdim

theorem coheight_le_one (x : X) (hx : f x = genericPoint Y) : coheight x ≤ 1 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ U from hxU)
  have hle : V ≤ f ⁻¹ᵁ U := hVU
  let x' : V := ⟨x, hxV⟩
  let y' : U := ⟨f x, hxU⟩
  let : Nonempty U := ⟨y'⟩
  let : Nonempty V := ⟨x'⟩
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (f ≫ g) V
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType g U hU
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType (f ≫ g) V hV
  let : Algebra A B := (f.appLE U V hle).hom.toAlgebra
  let : IsScalarTower K A B := by
    apply IsScalarTower.of_algebraMap_eq'
    have h := Scheme.Hom.appLE_comp_appLE f g ⊤ U V le_top hle
    exact (congrArg (fun t : Γ(Spec (.of K), ⊤) ⟶ B =>
      t.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) h).symm
  let q : PrimeSpectrum B := hV.primeIdealOf x'
  let i : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hc : i ≫ hU.fromSpec = hV.fromSpec ≫ f := hU.SpecMap_appLE_fromSpec f hV hle
  have hqx : hV.fromSpec q = x := hV.fromSpec_primeIdealOf x'
  have hiq : i q = genericPoint (Spec (.of A)) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact (congrArg (fun t : Spec (.of B) ⟶ Y => t q) hc).trans
      ((congrArg f hqx).trans (hx.trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm))
  have hq : q.asIdeal.under A = ⊥ := by
    change (i q).asIdeal = ⊥
    rw [hiq, genericPoint_eq_bot_of_affine]
    rfl
  have hAB : (Algebra.trdeg K A).toNat + 1 = (Algebra.trdeg K B).toNat := by
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections g U hU,
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (f ≫ g) V hV] at hdim
    exact hdim
  have hh := Relative.DivisorDimension.height_le_one_over_bot K A B hAB q.asIdeal hq
  rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hV.fromSpec,
    hV.fromSpec_primeIdealOf] at hh
  exact hh

theorem stalk_valuation (x : X) (hx : f x = genericPoint Y)
    [IsIntegrallyClosed (X.presheaf.stalk x)] : ValuationRing (X.presheaf.stalk x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ g)
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (coheight_le_one f g hdim x hx)
  exact CurveLocalRings.normal_local_valuation _

theorem image_eq_genericPoint (x : X) (hx : coheight x = 1) (hdeg : f.residueDegree x ≠ 0) :
    f x = genericPoint Y := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ U from hxU)
  have hle : V ≤ f ⁻¹ᵁ U := hVU
  let x' : V := ⟨x, hxV⟩
  let y' : U := ⟨f x, hxU⟩
  let : Nonempty U := ⟨y'⟩
  let : Nonempty V := ⟨x'⟩
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (f ≫ g) V
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType g U hU
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType (f ≫ g) V hV
  let : Algebra A B := (f.appLE U V hle).hom.toAlgebra
  let : IsScalarTower K A B := by
    apply IsScalarTower.of_algebraMap_eq'
    have h := Scheme.Hom.appLE_comp_appLE f g ⊤ U V le_top hle
    exact (congrArg (fun t : Γ(Spec (.of K), ⊤) ⟶ B =>
      t.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) h).symm
  let q : PrimeSpectrum B := hV.primeIdealOf x'
  let i : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hc : i ≫ hU.fromSpec = hV.fromSpec ≫ f := hU.SpecMap_appLE_fromSpec f hV hle
  have hqx : hV.fromSpec q = x := hV.fromSpec_primeIdealOf x'
  have hq : q.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hV.fromSpec,
      hV.fromSpec_primeIdealOf]
    exact hx
  have hd : q.asIdeal.inertiaDeg A ≠ 0 := by
    have ht := CyclePushforward.residueDegree_comp i hU.fromSpec q
    rw [hc, CyclePushforward.residueDegree_comp,
      Principal.ClosedSectionCycle.residueDegree_immersion hV.fromSpec q,
      Principal.ClosedSectionCycle.residueDegree_immersion hU.fromSpec (i q), Nat.one_mul, Nat.mul_one] at ht
    intro hz
    apply hdeg
    exact (congrArg f.residueDegree hqx).symm.trans (ht.trans
      ((Affine.ResidueDegree.residueDegree_eq_inertiaDeg A B q).trans hz))
  have hAB : (Algebra.trdeg K A).toNat + 1 = (Algebra.trdeg K B).toNat := by
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections g U hU,
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (f ≫ g) V hV] at hdim
    exact hdim
  have hp := Relative.DivisorDimension.under_eq_bot_of_height_one_of_degree K A B hAB q.asIdeal hq hd
  have hiq : i q = genericPoint (Spec (.of A)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  have hpoint := congrArg (fun t : Spec (.of B) ⟶ Y => t q) hc
  change hU.fromSpec (i q) = f (hV.fromSpec q) at hpoint
  exact (congrArg f hqx).symm.trans (hpoint.symm.trans
    ((congrArg hU.fromSpec hiq).trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec)))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberDimension
