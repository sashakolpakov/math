import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL

/-! # Isogeny Frame Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Transport a split source frame through an actual rational Tate
isogeny. Target integral lattices and subsequent isogeny preimages are
then expressed in exactly the original source coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section Linear
variable {R F V W U : Type*} [CommRing R] [Field F] [Algebra R F]
  [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
  [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower R F U]

theorem IsogenyFrameTransport.comap_equiv_map_frame (L : Submodule R W) (a : V ≃ₗ[F] W) (e : V ≃ₗ[F] U) :
    (L.comap (a.toLinearMap.restrictScalars R)).map (e.toLinearMap.restrictScalars R) =
      L.map ((a.symm.trans e).toLinearMap.restrictScalars R) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a x, hx, congrArg e (a.symm_apply_apply x)⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨a.symm y, ?_, rfl⟩
    change a (a.symm y) ∈ L
    rw [LinearEquiv.apply_symm_apply]
    exact hy

end Linear

variable {R k : Type} [CommRing R] [Field k] [IsAlgClosed k]
  {g N s n : ℕ} {P Q : PEL.PELFamilyData R g N (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q n) (q : ℕ) [Fact q.Prime]
  (frame : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)

def PELIsogenies.PELIsogeny.targetFrame : Rational.SplitTateFrame s Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).symm.trans frame

theorem PELIsogenies.PELIsogeny.rationalTate_action (a : R)
    (z : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action a)) z) =
      Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        (End.endSchemeMap Q.abelian.scheme (Q.action a))
        (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny z) := by
  have h : Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (End.endSchemeMap P.abelian.scheme (P.action a) ≫ e.isogeny.hom) =
    Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (e.isogeny.hom ≫ End.endSchemeMap Q.abelian.scheme (Q.action a)) := by
    congr 1
    exact e.equivariant a
  simp only [Functor.rationalTateMap_comp] at h
  exact LinearMap.congr_fun h z

theorem PELIsogenies.PELIsogeny.targetFrame_equivariant (χ : Fin s × Bool → R →+* ℤ_[q])
    (hf : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q χ frame) :
    Rational.IsSplitActionFrame Q (Over.mk (𝟙 (Spec (.of k)))) q χ (e.targetFrame q frame) := by
  intro a z v i
  obtain ⟨z, rfl⟩ := (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).surjective z
  rw [← e.rationalTate_action q a z]
  simpa only [PELIsogenies.PELIsogeny.targetFrame, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hf a z v i

theorem PELIsogenies.PELIsogeny.targetFrame_integral :
    Rational.framedIntegralTateImage (e.targetFrame q frame) =
      (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom).map
        (frame.toLinearMap.restrictScalars ℤ_[q]) :=
  (IsogenyFrameTransport.comap_equiv_map_frame
    (Rational.integralTateImage Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny) frame).symm

theorem PELIsogenies.PELIsogeny.targetFrame_preimage {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (f : Q.abelian.scheme ⟶ A) [IsMonHom f] :
    (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f).map
        ((e.targetFrame q frame).toLinearMap.restrictScalars ℤ_[q]) =
      (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) (e.isogeny.hom ≫ f)).map
        (frame.toLinearMap.restrictScalars ℤ_[q]) := by
  rw [Lattices.isogenyTatePreimage_comp]
  exact (IsogenyFrameTransport.comap_equiv_map_frame _
    (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny) frame).symm

theorem PELIsogenies.PELIsogeny.targetFrame_lattice {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (f : Q.abelian.scheme ⟶ A) [IsMonHom f] (v : Fin s × Bool) :
    Rational.framedTateLattice (e.targetFrame q frame) f v =
      Rational.framedTateLattice frame (e.isogeny.hom ≫ f) v := by
  unfold Rational.framedTateLattice
  rw [e.targetFrame_preimage q frame f]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
