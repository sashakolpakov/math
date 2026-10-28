import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

/-! # Image Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ImageDimension

noncomputable section

/-! Native scheme residue degrees and affine prime heights show that
divisors with nonzero pushforward coefficients preserve codimension under
maps between integral finite-type schemes of equal dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem coheight_image_eq_one {K : Type} [Field K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g] [LocallyOfFiniteType (f ≫ g)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g))
    (x : X) (hx : coheight x = 1) (hdeg : f.residueDegree x ≠ 0) : coheight (f x) = 1 := by
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
  have hc : i ≫ hU.fromSpec = hV.fromSpec ≫ f :=
    hU.SpecMap_appLE_fromSpec f hV hle
  have hqx : hV.fromSpec q = x := hV.fromSpec_primeIdealOf x'
  have hp : i q = hU.primeIdealOf y' := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact (congrArg (fun t : Spec (.of B) ⟶ Y => t q) hc).trans
      ((congrArg f hqx).trans (hU.fromSpec_primeIdealOf y').symm)
  have hq : q.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hV.fromSpec,
      hV.fromSpec_primeIdealOf]
    exact hx
  have hd : q.asIdeal.inertiaDeg A ≠ 0 := by
    have ht := CyclePushforward.residueDegree_comp i hU.fromSpec q
    rw [hc, CyclePushforward.residueDegree_comp,
      Principal.ClosedSectionCycle.residueDegree_immersion hV.fromSpec q,
      Principal.ClosedSectionCycle.residueDegree_immersion hU.fromSpec (i q),
      Nat.one_mul, Nat.mul_one] at ht
    intro hz
    apply hdeg
    exact (congrArg f.residueDegree hqx).symm.trans (ht.trans
      ((Affine.ResidueDegree.residueDegree_eq_inertiaDeg A B q).trans hz))
  have hAB : (Algebra.trdeg K A).toNat = (Algebra.trdeg K B).toNat := by
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections g U hU,
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (f ≫ g) V hV] at hdim
    exact hdim
  have hheight := Affine.DivisorDimension.height_under_eq_one K A B hAB q.asIdeal hq hd
  have hheight' : (i q).asIdeal.height = 1 := hheight
  rw [hp, idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec,
    hU.fromSpec_primeIdealOf] at hheight'
  exact hheight'

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ImageDimension
