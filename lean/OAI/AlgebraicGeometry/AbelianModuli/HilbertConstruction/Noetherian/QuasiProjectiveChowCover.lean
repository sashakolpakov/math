import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveChowCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralClosedSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
import Mathlib.AlgebraicGeometry.Limits

/-! # Quasi Projective Chow Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasiProjectiveChowCover.NoetherianQuasiProjectiveChowCover

noncomputable section

/-! Finite proper covers of a Noetherian separated finite-type scheme
by integral schemes immersed in actual projective ambient schemes.
Reduced irreducible components are used only as auxiliary sources. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {C : Type u} [CommRing C] {X : Scheme.{u}}

structure Data (f : X ⟶ Spec (.of C)) where
  index : Type u
  finite : Finite index
  scheme : index → Scheme.{u}
  integral : ∀ i, IsIntegral (scheme i)
  projection : ∀ i, scheme i ⟶ X
  proper : ∀ i, IsProper (projection i)
  covers : ∀ x : X, ∃ (i : index) (z : scheme i), projection i z = x
  ambient : index → Over (Spec (.of C))
  projective : ∀ i, Projective.ProjectivePresentations.ProjectivePresentation (ambient i)
  embedding : ∀ i, scheme i ⟶ (ambient i).left
  immersion : ∀ i, IsImmersion (embedding i)
  quasiCompact : ∀ i, QuasiCompact (embedding i)
  embedding_base :
    ∀ i, embedding i ≫ (ambient i).hom = projection i ≫ f

def build [IsNoetherian X] (f : X ⟶ Spec (.of C))
    [IsSeparated f] [LocallyOfFiniteType f] : Data f := by
  classical
  let J : Type u := irreducibleComponents X
  have hJ : Finite J :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  let W (i : J) : Closeds X :=
    ⟨i.val, isClosed_of_mem_irreducibleComponents i.val i.property⟩
  let I : J → X.IdealSheafData :=
    fun i => Scheme.IdealSheafData.vanishingIdeal (W i)
  let D (i : J) :
      QuasiProjectiveChowCover.IntegralQuasiProjectiveChowCover.Data
        ((I i).subschemeι ≫ f) := by
    have : IsIntegral (I i).subscheme :=
      IntegralClosedSupport.vanishingIdeal_subscheme_integral (W i) i.property.1
    have : IsNoetherian (I i).subscheme :=
      HilbertConstruction.Finite.TypeParameterNoetherian.finiteType_noetherian_source (I i).subschemeι
    exact QuasiProjectiveChowCover.IntegralQuasiProjectiveChowCover.build
      ((I i).subschemeι ≫ f)
  let q (i : J) : (D i).scheme ⟶ X :=
    (D i).projection ≫ (I i).subschemeι
  have hq (i : J) : IsProper (q i) := by
    have : IsProper (D i).projection := (D i).proper
    change IsProper ((D i).projection ≫ (I i).subschemeι)
    infer_instance
  have hcover :
      ∀ x : X, ∃ (i : J) (z : (D i).scheme), q i z = x := by
    intro x
    let i : J :=
      ⟨irreducibleComponent x,
        irreducibleComponent_mem_irreducibleComponents x⟩
    have hr : Set.range (I i).subschemeι = (W i : Set X) := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Scheme.IdealSheafData.coe_support_vanishingIdeal (W i)
    have hx : x ∈ Set.range (I i).subschemeι := by
      rw [hr]
      change x ∈ irreducibleComponent x
      exact mem_irreducibleComponent
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, hz⟩ := (D i).surjective.surj y
    refine ⟨i, z, ?_⟩
    change ((D i).projection ≫ (I i).subschemeι) z = x
    rw [Scheme.Hom.comp_apply, hz]
    exact hy
  exact {
    index := J
    finite := hJ
    scheme := fun i => (D i).scheme
    integral := fun i => (D i).integral
    projection := q
    proper := hq
    covers := hcover
    ambient := fun i => (D i).ambient
    projective := fun i => (D i).projective
    embedding := fun i => (D i).embedding
    immersion := fun i => (D i).immersion
    quasiCompact := fun i => (D i).quasiCompact
    embedding_base := fun i =>
      (D i).embedding_base.trans
        (Category.assoc (D i).projection (I i).subschemeι f).symm
  }

theorem Data.sigmaProjection_surjective
    {f : X ⟶ Spec (.of C)} (D : Data f) :
    Surjective (Sigma.desc D.projection) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, z, hz⟩ := D.covers x
  exact Set.mem_iUnion.mpr ⟨i, z, hz⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasiProjectiveChowCover.NoetherianQuasiProjectiveChowCover
