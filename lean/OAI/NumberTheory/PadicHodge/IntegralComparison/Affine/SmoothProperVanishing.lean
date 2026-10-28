import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SchemeIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GlobalFunctionScheme
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FiberSchemeIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.HigherCrystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Higher
import OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyCrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyEtaleCohomology

/-! # Smooth Proper Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProperVanishing

noncomputable section

/-! Original positive cohomology vanishes for every affine smooth proper projective scheme over a finite field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [IsAffine X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k A

local instance : IsSeparated (Crystalline.Presentation.affineScheme k A).hom :=
  inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k A))))

include hprojective in
theorem crystalline (i : ℕ) : Subsingleton (Witt.Crystalline.rationalCohomology p k X (i + 1)) := by
  rcases isEmpty_or_nonempty X.left with h | h
  · let : IsEmpty X.left := h
    exact EmptyCrystallineCohomology.rational p k X (i + 1)
  · let : Nonempty X.left := h
    let : Nontrivial A := SmoothProper.GlobalFunctionAlgebra.nontrivial k X
    let : Module.Finite k A := SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective
    let : Algebra.Etale k A := SmoothProper.GlobalFunctionAlgebra.etale k X p hprojective
    let : Subsingleton (Witt.Crystalline.rationalCohomology p k Y (i + 1)) :=
      FiniteEtale.HigherCrystalline.rational p k A i
    exact (Crystalline.SchemeIso.rational p k
      (GlobalFunctionScheme.iso k X) (i + 1)).symm.injective.subsingleton

include p hprojective in
theorem etale (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    Subsingleton (Interfaces.EtaleCohomology ℓ k X.hom (i + 1)) := by
  rcases isEmpty_or_nonempty X.left with h | h
  · let : IsEmpty X.left := h
    let : IsEmpty (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) X.hom) :=
      ⟨fun x => @IsEmpty.false X.left inferInstance
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) x)⟩
    exact EmptyEtaleCohomology.cohomology ℓ _ (i + 1)
  · let : Nonempty X.left := h
    let : Module.Finite k A := SmoothProper.GlobalFunctionAlgebra.module_finite k X hprojective
    let : Algebra.Etale k A := SmoothProper.GlobalFunctionAlgebra.etale k X p hprojective
    let : Subsingleton (Interfaces.EtaleCohomology ℓ k (Y).hom (i + 1)) :=
      FiniteEtale.Higher.Etale.vanishing k A ℓ i
    exact (Geometric.FiberSchemeIso.cohomology k
      (GlobalFunctionScheme.iso k X) ℓ (i + 1)).injective.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProperVanishing
