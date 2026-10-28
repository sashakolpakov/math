import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicGeometry.Restrict

/-! # Contraction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction.CechContraction

noncomputable section

/-!
# Cohomology: local contraction of the Čech nerve

When a member of the family is the whole open, inserting that member gives
an extra degeneracy. This is the local splitting used in Čech descent.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- Over a lattice of opens, a map of formal coproducts is determined by
its function on components. -/
theorem hom_ext_indices {S T : FormalCoproduct.{u} X.Opens} {f g : S ⟶ T}
    (h : f.f = g.f) : f = g :=
  FormalCoproduct.hom_ext h (fun _ => Subsingleton.elim _ _)

/-- The Čech nerve augmented to the whole scheme. -/
def augmented : SimplicialObject.Augmented (FormalCoproduct.{u} X.Opens) where
  left := (FormalCoproduct.mk ι U).cech
  right := (FormalCoproduct.incl X.Opens).obj ⊤
  hom :=
    { app _ := { f := fun _ => PUnit.unit, φ := fun _ => homOfLE le_top }
      naturality _ _ _ := hom_ext_indices X rfl }

variable (i₀ : ι) (hU : U i₀ = ⊤)

/-- Select the whole-open member in degree zero. -/
def sectionZero : (augmented X U).right ⟶ (augmented X U).left _⦋0⦌ where
  f _ _ := i₀
  φ _ := Pi.lift (fun _ => homOfLE (by change ⊤ ≤ U i₀; rw [hU]))

/-- Insert the whole-open member at the start of a tuple. -/
def insert (n : ℕ) : (augmented X U).left _⦋n⦌ ⟶ (augmented X U).left _⦋n + 1⦌ where
  f v := Fin.cons i₀ v
  φ v := Pi.lift (Fin.cases (homOfLE (by
      change (∏ᶜ (U ∘ v)) ≤ U i₀
      rw [hU]
      exact le_top))
    (fun j => Pi.π (U ∘ v) j))

/-- The insertion satisfies the simplicial contraction identities. -/
def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy (augmented X U) where
  s' := sectionZero X U i₀ hU
  s := insert X U i₀ hU
  s'_comp_ε := by
    apply hom_ext_indices X
    funext v
    cases v
    rfl
  s₀_comp_δ₁ := by
    apply hom_ext_indices X
    funext v j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    apply hom_ext_indices X
    funext v j
    change Fin (n + 1) → ι at v
    change Fin (n + 1) at j
    change (Fin.cons i₀ v : Fin (n + 2) → ι) (Fin.succAbove 0 j) = v j
    simp
  s_comp_δ n i := by
    apply hom_ext_indices X
    funext v j
    change Fin (n + 2) → ι at v
    change Fin (n + 2) at j
    change (Fin.cons i₀ v : Fin (n + 3) → ι) (i.succ.succAbove j) =
      (Fin.cons i₀ (fun a => v (i.succAbove a)) : Fin (n + 2) → ι) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  s_comp_σ n i := by
    apply hom_ext_indices X
    funext v j
    change Fin (n + 1) → ι at v
    change Fin (n + 3) at j
    change (Fin.cons i₀ v : Fin (n + 2) → ι) (i.succ.predAbove j) =
      (Fin.cons i₀ (fun a => v (i.predAbove a)) : Fin (n + 3) → ι) j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp

/-- Every presheaf sends the local splitting to a splitting of its
augmented Čech diagram, viewed in the opposite coefficient category. -/
def coefficientsExtraDegeneracy (R : Type u) [CommRing R]
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) :=
  (extraDegeneracy X U i₀ hU).map
    (((FormalCoproduct.evalOp X.Opens (ModuleCat.{u} R)).obj P).rightOp)

/-- The split local Čech diagram is homotopy equivalent to its augmentation. -/
def coefficientsHomotopyEquiv (R : Type u) [CommRing R]
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) :=
  (coefficientsExtraDegeneracy X U i₀ hU R P).homotopyEquiv

variable (i : ι)

/-- Pull the whole family back to one of its open subschemes. -/
def restrictedFamily (j : ι) : (U i).toScheme.Opens := (U i).ι ⁻¹ᵁ U j

@[simp]
theorem restrictedFamily_self : restrictedFamily X U i i = ⊤ :=
  (U i).ι_preimage_self

/-- The pulled-back Čech nerve always has an explicit contraction on a
member of the family. -/
def localExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy
      (augmented (U i).toScheme (restrictedFamily X U i)) :=
  extraDegeneracy (U i).toScheme (restrictedFamily X U i) i (restrictedFamily_self X U i)

/-- Restrict the coefficient presheaf to an open subscheme. -/
def restrictedCoefficients (R : Type u) [CommRing R]
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) : (U i).toScheme.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (U i).ι.opensFunctor.op ⋙ P

/-- Local Čech exactness is supplied by a homotopy equivalence on each
member of the family, with the actual restricted coefficients. -/
def localCoefficientsHomotopyEquiv (R : Type u) [CommRing R]
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) :=
  coefficientsHomotopyEquiv (U i).toScheme (restrictedFamily X U i) i
    (restrictedFamily_self X U i) R (restrictedCoefficients X U i R P)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Contraction.CechContraction
