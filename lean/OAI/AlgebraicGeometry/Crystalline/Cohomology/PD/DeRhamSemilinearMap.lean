import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearA
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # De Rham Semilinear Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap

noncomputable section

/-! # Semilinear pullback on the original divided-power differential forms -/

open _root_.CategoryTheory

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (σ : R →+* S) (f : A →+* B)
  (h : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal B) (δJ : DividedPowers J)
  (hf : DividedPowers.IsDPMorphism δI δJ f)

def ordinary (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₛₗ[f] DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMapA R S A B σ f h n

theorem ordinary_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    ordinary R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      DeRhamPresentationTo.DeRhamPresentation.symbol S B (f a) (f ∘ v) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol R S A B σ f h n a v

def relationMap {n : ℕ} (t : DeRham.PDDeRham.RelationIndex A I n) : DeRham.PDDeRham.RelationIndex B J n where
  v := f ∘ t.v
  i := t.i
  x := ⟨f t.x, hf.ideal_comp (Ideal.mem_map_of_mem f t.x.property)⟩
  m := t.m

theorem ordinary_relation {n : ℕ} (t : DeRham.PDDeRham.RelationIndex A I n) :
    ordinary R S A B σ f h n (DeRham.PDDeRham.relation R A I δI n t) =
      DeRham.PDDeRham.relation S B J δJ n (relationMap A B f I δI J δJ hf t) := by
  simp only [DeRham.PDDeRham.relation, relationMap, map_sub, ordinary_symbol, map_one,
    DeRhamSemilinearA.DeRhamSemilinearMap.comp_update]
  rw [hf.map_dpow t.x.property, hf.map_dpow t.x.property]

include hf in
theorem ordinary_mem {n : ℕ} (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (hω : ω ∈ DeRham.PDDeRham.relations R A I δI n) :
    ordinary R S A B σ f h n ω ∈ DeRham.PDDeRham.relations S B J δJ n := by
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨t, rfl⟩ := hω
    rw [ordinary_relation R S A B σ f h I δI J δJ hf]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add ω η hω hη ihω ihη => rw [map_add]; exact Submodule.add_mem _ ihω ihη
  | smul a ω hω ihω => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ihω

def formMapA (n : ℕ) : DeRham.PDDeRham.Form R A I δI n →ₛₗ[f] DeRham.PDDeRham.Form S B J δJ n :=
  (DeRham.PDDeRham.relations R A I δI n).mapQ (DeRham.PDDeRham.relations S B J δJ n)
    (ordinary R S A B σ f h n) (fun ω hω => ordinary_mem R S A B σ f h I δI J δJ hf ω hω)

def formMap (n : ℕ) : DeRham.PDDeRham.Form R A I δI n →ₛₗ[σ] DeRham.PDDeRham.Form S B J δJ n where
  __ := (formMapA R S A B σ f h I δI J δJ hf n).toAddMonoidHom
  map_smul' r ω := by
    change formMapA R S A B σ f h I δI J δJ hf n (r • ω) =
      σ r • formMapA R S A B σ f h I δI J δJ hf n ω
    rw [← algebraMap_smul A r ω, map_smulₛₗ, h, algebraMap_smul]

theorem formMap_mk (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap R S A B σ f h I δI J δJ hf n ((DeRham.PDDeRham.relations R A I δI n).mkQ ω) =
      (DeRham.PDDeRham.relations S B J δJ n).mkQ (DeRhamSemilinearA.DeRhamSemilinearMap.formMap R S A B σ f h n ω) := rfl

theorem formMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formMap R S A B σ f h I δI J δJ hf n (DeRham.PDDeRham.symbol R A I δI a v) =
      DeRham.PDDeRham.symbol S B J δJ (f a) (f ∘ v) := by
  change (DeRham.PDDeRham.relations S B J δJ n).mkQ
    (ordinary R S A B σ f h n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [ordinary_symbol]
  rfl

theorem formMap_differential (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δI n) :
    formMap R S A B σ f h I δI J δJ hf (n + 1) (DeRham.PDDeRham.differential R A I δI n ω) =
      DeRham.PDDeRham.differential S B J δJ n (formMap R S A B σ f h I δI J δJ hf n ω) := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  rw [DeRham.PDDeRham.differential_mk, formMap_mk, formMap_mk, DeRham.PDDeRham.differential_mk,
    DeRhamSemilinearA.DeRhamSemilinearMap.formMap_differential]

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map σ
    (DeRham.PDDeRham.complex R A I δI) (DeRham.PDDeRham.complex S B J δJ) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.ofSuccessors
    (fun n => formMap R S A B σ f h I δI J δJ hf n) (by
      intro n ω
      dsimp only [DeRham.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      exact formMap_differential R S A B σ f h I δI J δJ hf n ω)

theorem addHom_ext (n : ℕ) {M : Type*} [AddCommMonoid M]
    (g j : DeRham.PDDeRham.Form R A I δI n →+ M)
    (hs : ∀ a v, g (DeRham.PDDeRham.symbol R A I δI a v) = j (DeRham.PDDeRham.symbol R A I δI a v)) : g = j := by
  apply AddMonoidHom.ext
  intro ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δI n) ω
  exact DFunLike.congr_fun (DeRhamSemilinearA.DeRhamSemilinearMap.addHom_ext R A n
    (g.comp (DeRham.PDDeRham.relations R A I δI n).mkQ.toAddMonoidHom)
    (j.comp (DeRham.PDDeRham.relations R A I δI n).mkQ.toAddMonoidHom) hs) ω

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap
