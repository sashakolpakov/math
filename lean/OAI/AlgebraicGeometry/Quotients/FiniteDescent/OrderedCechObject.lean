import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech
import Mathlib.LinearAlgebra.DFinsupp

/-! # Ordered Cech Object -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechObject.Construction.OrderedCechFlat

noncomputable section

/-! Every term of a finite affine ordered Cech complex is flat over a flat base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [Flat f]
variable (M : X.Modules) (hM : SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)

include hM in
theorem object (q : ℕ)
    (hU : ∀ i : Fin (q + 1) → ι, IsAffineOpen (∏ᶜ fun k : Fin (q + 1) => U (i k))) :
    Module.Flat Γ(S, ⊤) (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject f M U q) := by
  classical
  have : Finite (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) := inferInstanceAs
    (Finite {i : Fin (q + 1) → ι // StrictMono i})
  let : Fintype (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) := Fintype.ofFinite _
  have : ∀ i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q, Module.Flat Γ(S, ⊤) (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f M U q i.1) :=
    fun i => BaseSections.Construction.BaseSectionsFlat.flat f M hM ⟨_, hU i.1⟩
  have : Module.Flat Γ(S, ⊤) (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechTerm f M U q) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := Γ(S, ⊤))
        (M := fun i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q => ↥(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f M U q i.1))).symm
  exact Module.Flat.of_linearEquiv (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObjectIsoPi f M U q).toLinearEquiv

include hM in
theorem complex (hU : ∀ q (i : Fin (q + 1) → ι),
    IsAffineOpen (∏ᶜ fun k : Fin (q + 1) => U (i k))) (q : ℕ) :
    Module.Flat Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U).X q) :=
  object f M hM U q (hU q)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechObject.Construction.OrderedCechFlat
