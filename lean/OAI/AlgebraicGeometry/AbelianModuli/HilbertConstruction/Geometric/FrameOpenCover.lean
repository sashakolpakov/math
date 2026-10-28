import Mathlib.AlgebraicGeometry.ResidueField
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Polynomials
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Frame Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FrameOpenCover

noncomputable section

/-! Frame existence on every geometric fiber gives a finite principal
open cover of the base by its actual labeled determinant loci. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

def fieldPointGlobalScalarMap {S : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ S) : Γ(S, ⊤) →+* K :=
  (Scheme.ΓSpecIso (.of K)).hom.hom.comp f.appTop.hom

theorem fieldPoint_mem_basicOpen_of_unit {S : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ S) (a : Γ(S, ⊤))
    (ha : IsUnit (fieldPointGlobalScalarMap f a)) :
    f (IsLocalRing.closedPoint K) ∈ S.basicOpen a := by
  have hunit : IsUnit (f.appTop a) := by
    let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    have h := ha.map e.symm.toRingHom
    change IsUnit (e.symm (e (f.appTop a))) at h
    rwa [e.symm_apply_apply] at h
  have hpre : f ⁻¹ᵁ S.basicOpen a = ⊤ :=
    (f.preimage_basicOpen_top a).trans ((Spec (.of K)).basicOpen_of_isUnit hunit)
  exact (show IsLocalRing.closedPoint K ∈ f ⁻¹ᵁ S.basicOpen a from hpre.symm ▸ trivial)

def labeledFrameOpen {S : Scheme.{u}} {r m : ℕ}
    (v : Fin m → Fin r → Γ(S, ⊤)) (a : (Fin r → Fin m) × Fin m) : S.Opens :=
  S.basicOpen (ProjectiveFrame.Polynomials.labeledFrameDiscriminant a.1 a.2 v)

theorem geometricFrames_cover_principalOpens {S : Scheme.{u}} {r m : ℕ}
    (v : Fin m → Fin r → Γ(S, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S),
      Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r)
        (fun i k => fieldPointGlobalScalarMap f (v i k))) :
    ∀ x : S, ∃ a : (Fin r → Fin m) × Fin m, x ∈ labeledFrameOpen v a := by
  intro x
  let K := AlgebraicClosure (S.residueField x)
  let f : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫ S.fromSpecResidueField x
  have hf : f (IsLocalRing.closedPoint K) = x := S.fromSpecResidueField_apply x _
  obtain ⟨b, σ, hb, j, hj⟩ := h K f
  have hu : IsUnit (fieldPointGlobalScalarMap f (ProjectiveFrame.Polynomials.labeledFrameDiscriminant σ j v)) := by
    unfold ProjectiveFrame.Polynomials.labeledFrameDiscriminant
    rw [ProjectiveFrame.Polynomials.vectorFrameDiscriminant_map]
    apply (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant_isUnit_iff (Pi.basisFun K (Fin r)) _ _).mpr
    exact ⟨b, hb, fun k => isUnit_iff_ne_zero.mpr (hj k)⟩
  refine ⟨(σ, j), ?_⟩
  exact hf ▸ fieldPoint_mem_basicOpen_of_unit f _ hu

def geometricFramePrincipalOpenCover {S : Scheme.{u}} {r m : ℕ}
    (v : Fin m → Fin r → Γ(S, ⊤))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S),
      Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r)
        (fun i k => fieldPointGlobalScalarMap f (v i k))) : Scheme.OpenCover.{0} S where
  I₀ := (Fin r → Fin m) × Fin m
  X a := (labeledFrameOpen v a).toScheme
  f a := (labeledFrameOpen v a).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨a, ha⟩ := geometricFrames_cover_principalOpens v h x
    exact ⟨a, ⟨⟨x, ha⟩, rfl⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FrameOpenCover
