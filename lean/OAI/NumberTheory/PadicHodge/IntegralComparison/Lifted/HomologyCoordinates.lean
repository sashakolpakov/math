import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Homology Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates

noncomputable section

/-! The canonical universe-lift comparison for actual module cohomology commutes with every cochain map. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type u) [CommRing R]

def complex (K : CochainComplex (ModuleCat.{v} R) ℕ) : CochainComplex (ModuleCat.{max v w} R) ℕ :=
  ((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).obj K

def equivalence (K : CochainComplex (ModuleCat.{v} R) ℕ) (i : ℕ) : K.homology i ≃ₗ[R] (complex.{u, v, w} R K).homology i :=
  ULift.moduleEquiv.symm.trans (((K.sc i).mapHomologyIso (ModuleCat.uliftFunctor.{w, v} R)).symm.toLinearEquiv)

theorem naturality {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (i : ℕ) (x : K.homology i) :
    HomologicalComplex.homologyMap (((ModuleCat.uliftFunctor.{w, v} R).mapHomologicalComplex (.up ℕ)).map f) i
      (equivalence.{u, v, w} R K i x) = equivalence.{u, v, w} R L i (HomologicalComplex.homologyMap f i x) := by
  let U := ModuleCat.uliftFunctor.{w, v} R
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map f) U
  exact (congrArg (fun a => a (ULift.up x)) h).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates
