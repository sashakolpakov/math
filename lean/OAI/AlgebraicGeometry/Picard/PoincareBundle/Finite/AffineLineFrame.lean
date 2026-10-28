import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification
import Mathlib.RingTheory.Artinian.Module

/-! # Affine Line Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineFrame

noncomputable section

/-! Every line on a finite affine scheme over a field has an actual global frame, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Module.Finite k R]
  (L : Line.Bundles.LineBundle (Spec (.of R)))

include k

/-- Semilocal triviality of the Picard group gives a genuine global sheaf isomorphism. -/
theorem exists_frame : Nonempty (L.sheaf ≅ Line.Bundles.unitLine (Spec (.of R))) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  let M := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj L.sheaf
  have : Module.Invertible R M := Affine.Classification.globalSections_invertible L
  have : Module.Free R M := inferInstance
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := M)).mp inferInstance
  let eM : M ≅ ModuleCat.of R R := e.toModuleIso
  exact ⟨(QuasiCoherent.affineTildeIso L).symm ≪≫
    (tilde.functor (CommRingCat.of R)).mapIso eM ≪≫ tildeSelf⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AffineLineFrame
