import Mathlib.AlgebraicGeometry.Morphisms.Proper
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.Generators

/-! # Proper Affine Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover

noncomputable section

/-!
# IntegralComparison: finite affine coordinates supplied by proper geometry

Properness gives a finite affine cover. Its actual coordinate rings are
finite-type algebras over the ground field, so each chart has finitely
many polynomial generators. No cohomological finiteness is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

include f in
theorem compact : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f

def cover : X.OpenCover := by
  let : CompactSpace X := compact f
  exact X.affineCover.finiteSubcover

instance cover_fintype : Fintype (cover f).I₀ := by
  let : CompactSpace X := compact f
  unfold cover
  infer_instance

instance chart_affine (i : (cover f).I₀) : IsAffine ((cover f).X i) := by
  let : CompactSpace X := compact f
  change X.affineCover.finiteSubcover.I₀ at i
  change IsAffine (X.affineCover.finiteSubcover.X i)
  exact Scheme.isAffine_affineCover X (X.affineCover.idx i.val)

def coordinateRing (i : (cover f).I₀) : CommRingCat.{u} := Γ((cover f).X i, ⊤)

def chartIso (i : (cover f).I₀) : (cover f).X i ≅ Spec (coordinateRing f i) :=
  ((cover f).X i).isoSpec

def chartMap (i : (cover f).I₀) : Spec (coordinateRing f i) ⟶ X :=
  (chartIso f i).inv ≫ (cover f).f i

instance chartMap_open (i : (cover f).I₀) : IsOpenImmersion (chartMap f i) := by
  unfold chartMap
  infer_instance

theorem chartMap_range (i : (cover f).I₀) :
    (chartMap f i).opensRange = ((cover f).f i).opensRange :=
  Scheme.Hom.opensRange_comp_of_isIso _ _

theorem chartMaps_cover : (⨆ i, (chartMap f i).opensRange) = ⊤ := by
  simp_rw [chartMap_range]
  exact (cover f).iSup_opensRange

instance coordinateAlgebra (i : (cover f).I₀) : Algebra k (coordinateRing f i) :=
  (Spec.preimage (chartMap f i ≫ f)).hom.toAlgebra

theorem chartMap_over (i : (cover f).I₀) :
    chartMap f i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing f i))) :=
  (Spec.map_preimage _).symm

instance coordinate_finiteType (i : (cover f).I₀) : Algebra.FiniteType k (coordinateRing f i) := by
  have h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing f i)))) := by
    rw [← chartMap_over f i]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h

/-- Every chart in the finite proper cover has a finite polynomial presentation. -/
theorem chart_generators (i : (cover f).I₀) :
    ∃ (σ : Type u) (_ : Fintype σ) (x : σ → coordinateRing f i),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] coordinateRing f i) :=
  Finite.Generators.exists_generators k (coordinateRing f i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover
