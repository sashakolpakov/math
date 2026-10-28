import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalClasses
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # CM Global Sheaf Cycles -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMGlobalSheafCycles

noncomputable section

section

/-! # Actual cycles survive the original filtration inclusion in retained degrees -/

open _root_.CategoryTheory Limits

/-- A map that is an isomorphism in a cochain degree and monic in the next
degree is an isomorphism on actual cycles in that degree. -/
theorem cochainCyclesMap_isIso {K L : CochainComplex AddCommGrpCat ℤ}
    (f : K ⟶ L) (p : ℤ) [IsIso (f.f p)] [Mono (f.f ((ComplexShape.up ℤ).next p))] :
    IsIso (HomologicalComplex.cyclesMap f p) := by
  let s := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) p).map f
  have : IsIso s.τ₂ := by
    simpa only [s, HomologicalComplex.shortComplexFunctor_map_τ₂,
      HomologicalComplex.shortComplexFunctor_obj_X₂] using!
      (inferInstance : IsIso (f.f p))
  have : Mono s.τ₃ := by
    simpa only [s, HomologicalComplex.shortComplexFunctor_map_τ₃,
      HomologicalComplex.shortComplexFunctor_obj_X₃] using!
      (inferInstance : Mono (f.f ((ComplexShape.up ℤ).next p)))
  exact ShortComplex.isIso_cyclesMap_of_isIso_of_mono' s inferInstance inferInstance

variable (Y : TopCat.{0})

local notation "Γ" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y) (ComplexShape.up ℤ)

/-- Taking actual global sections retains the canonical isomorphism in every
degree included by the unchanged original stupid truncation. -/
theorem globalStupidTruncInclusion_component_isIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (p : ℤ) (n : ℕ)
    {j : ℤ} (h : (ComplexShape.embeddingUpIntGE p).f n = j) :
    IsIso (((Γ).map
        (OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))).f
          j) := by
  have : IsIso ((OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K
      (ComplexShape.embeddingUpIntGE p)).f j) := by
    rw [OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion_f K _ h]
    infer_instance
  change IsIso ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).map _)
  infer_instance

/-- Closed global forms have unique cycle lifts through the original lowest
filtered degree; no lifting assumption is supplied. -/
theorem globalStupidTruncInclusion_cycles_isIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (p : ℤ) :
    IsIso (HomologicalComplex.cyclesMap
      ((Γ).map
          (OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))) p) := by
  have : IsIso (((Γ).map
        (OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))).f p) := by
    exact globalStupidTruncInclusion_component_isIso Y K p 0 (by
      change p + (0 : ℕ) = p
      simp)
  have : IsIso (((Γ).map
        (OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))).f
          (p + 1)) := by
    exact globalStupidTruncInclusion_component_isIso Y K p 1 (by
      change p + (1 : ℕ) = p + 1
      norm_num)
  have hn : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp)
  have : Mono (((Γ).map (OAI.Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K
      (ComplexShape.embeddingUpIntGE p))).f ((ComplexShape.up ℤ).next p)) := by
    rw [hn]
    infer_instance
  exact cochainCyclesMap_isIso _ p

end

section

/-! # Actual closed global sheaf sections give original integer-indexed cycles -/

open _root_.CategoryTheory

variable (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ)

local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y

/-- A global section transported by the actual extension-by-zero component
isomorphism, with no choice of cohomology comparison. -/
def sheafExtendedGlobalSection (p : ℕ)
    (θ : (K.X p).presheaf.obj (Opposite.op ⊤)) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (K.extend ComplexShape.embeddingUpNat)).X (p : ℤ) :=
  (Γ).map (K.extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv θ

set_option backward.isDefEq.respectTransparency false in
/-- This actual section is closed in the original integer-indexed global complex. -/
theorem sheafExtendedGlobalSection_closed (p : ℕ)
    (θ : (K.X p).presheaf.obj (Opposite.op ⊤))
    (hθ : (K.d p (p + 1)).hom.app (Opposite.op ⊤) θ = 0) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (K.extend ComplexShape.embeddingUpNat)).d
      (p : ℤ) ((p + 1 : ℕ) : ℤ) (sheafExtendedGlobalSection Y K p θ) = 0 := by
  have hd :
      (K.extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv ≫
        (K.extend ComplexShape.embeddingUpNat).d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
      K.d p (p + 1) ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1)
          (i' := ((p + 1 : ℕ) : ℤ)) rfl).inv := by
    rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
      (i := p) (j := p + 1) (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) rfl rfl]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hv := ConcreteCategory.congr_hom (congrArg (fun f => (Γ).map f) hd) θ
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply] at hv
  change _ = ((Γ).map
    (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1)
      (i' := ((p + 1 : ℕ) : ℤ)) rfl).inv)
      ((K.d p (p + 1)).hom.app (Opposite.op ⊤) θ) at hv
  rw [hθ, map_zero] at hv
  exact hv

end

/-! # Retained global sections and closedness through actual extension by zero -/

open _root_.CategoryTheory

variable (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ)

local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y

/-- Recover the actual natural-degree global section from its retained integer degree. -/
def sheafRetainedGlobalSection (p : ℕ)
    (ζ : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
      (K.extend ComplexShape.embeddingUpNat)).X (p : ℤ)) :
    (K.X p).presheaf.obj (Opposite.op ⊤) :=
  (Γ).map (K.extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).hom ζ

/-- Recovery followed by extension returns the same actual global section. -/
theorem sheafExtendedGlobalSection_retained (p : ℕ)
    (ζ : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
      (K.extend ComplexShape.embeddingUpNat)).X (p : ℤ)) :
    sheafExtendedGlobalSection Y K p (sheafRetainedGlobalSection Y K p ζ) = ζ := by
  let e := K.extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl
  have h := congrArg (fun f => (Γ).map f) e.hom_inv_id
  simpa only [Functor.map_comp, Functor.map_id, AddCommGrpCat.comp_apply,
    AddCommGrpCat.id_apply] using! ConcreteCategory.congr_hom h ζ

set_option backward.isDefEq.respectTransparency false in
/-- A closed retained section is closed in the actual original natural-degree complex. -/
theorem sheafRetainedGlobalSection_closed (p : ℕ)
    (ζ : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
      (K.extend ComplexShape.embeddingUpNat)).X (p : ℤ))
    (hζ : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
      (K.extend ComplexShape.embeddingUpNat)).d
        (p : ℤ) ((p + 1 : ℕ) : ℤ) ζ = 0) :
    (K.d p (p + 1)).hom.app (Opposite.op ⊤) (sheafRetainedGlobalSection Y K p ζ) = 0 := by
  have hd : (K.extend ComplexShape.embeddingUpNat).d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫
      (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1)
        (i' := ((p + 1 : ℕ) : ℤ)) rfl).hom =
    (K.extendXIso ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).hom ≫
      K.d p (p + 1) := by
    rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
      (i := p) (j := p + 1) (i' := (p : ℤ)) (j' := ((p + 1 : ℕ) : ℤ)) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := ConcreteCategory.congr_hom (congrArg (fun f => (Γ).map f) hd) ζ
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply] at hv
  change ((Γ).map
      (K.extendXIso ComplexShape.embeddingUpNat (i := p + 1)
        (i' := ((p + 1 : ℕ) : ℤ)) rfl).hom)
        ((Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
          (K.extend ComplexShape.embeddingUpNat)).d (p : ℤ) ((p + 1 : ℕ) : ℤ) ζ) =
    (K.d p (p + 1)).hom.app (Opposite.op ⊤) (sheafRetainedGlobalSection Y K p ζ) at hv
  rw [hζ, map_zero] at hv
  exact hv.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMGlobalSheafCycles
