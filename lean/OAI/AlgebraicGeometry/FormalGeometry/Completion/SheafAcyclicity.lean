import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! # Sheaf Acyclicity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SheafAcyclicity.Construction

noncomputable section

/-!
# Completion: cohomology at a terminal object with trivial covering sieves

If every covering sieve at a terminal object is maximal, evaluation there
preserves epimorphisms. The constant integer sheaf is then projective, and
all positive-degree cohomology vanishes.
-/

open _root_.CategoryTheory Limits Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {T : C}

/-- With no proper covering sieve at `T`, epimorphisms of abelian sheaves
are surjective on sections at `T`. -/
theorem sheaf_epi_app_surjective_of_coveringSieve_eq_top
    (hT : ∀ S : Sieve T, S ∈ J T → S = ⊤)
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op T)) := by
  have : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat f).mpr inferInstance
  intro x
  have h := hT _ (Presheaf.imageSieve_mem J f.hom x)
  have hx := (Sieve.id_mem_iff_eq_top).mpr h
  simpa [Presheaf.imageSieve] using hx

/-- The integer group with the same universe as the sheaf values is projective. -/
theorem projective_ulift_int : Projective (AddCommGrpCat.of (ULift.{w} ℤ)) where
  factors {E X} f e _ := by
    obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance (f (ULift.up 1))
    refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom E v), ?_⟩
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv X).injective
    change e ((1 : ℤ) • v) = f (ULift.up 1)
    simpa only [one_zsmul] using hv

/-- The constant integer sheaf is projective when terminal covering sieves
are trivial. -/
theorem projective_constant_int_of_coveringSieve_eq_top (hterminal : IsTerminal T)
    (hT : ∀ S : Sieve T, S ∈ J T → S = ⊤) :
    Projective ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) := by
  have : ((sheafSections J AddCommGrpCat.{w}).obj (op T)).PreservesEpimorphisms :=
    ⟨fun f _ ↦ ConcreteCategory.epi_of_surjective _
      (sheaf_epi_app_surjective_of_coveringSieve_eq_top hT f)⟩
  exact (constantSheafAdj J AddCommGrpCat.{w} hterminal).map_projective _ projective_ulift_int

/-- Every abelian sheaf has zero positive-degree cohomology when terminal
covering sieves are trivial. -/
theorem sheaf_cohomology_eq_zero_of_coveringSieve_eq_top (hterminal : IsTerminal T)
    (hT : ∀ S : Sieve T, S ∈ J T → S = ⊤)
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H (n + 1)) : x = 0 := by
  have := projective_constant_int_of_coveringSieve_eq_top hterminal hT
  exact Abelian.Ext.eq_zero_of_projective x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SheafAcyclicity.Construction
