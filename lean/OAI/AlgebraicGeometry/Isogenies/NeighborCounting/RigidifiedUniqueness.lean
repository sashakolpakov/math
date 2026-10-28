import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections

/-! # Rigidified Uniqueness -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedUniqueness

noncomputable section

/-! Uniqueness of normalized line-bundle isomorphisms, including after
arbitrary nonreduced base change of a proper integral geometric factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

variable {X T : Scheme.{u}} (π : X ⟶ T) (z : T ⟶ X)

theorem section_appTop_injective (hπ : z ≫ π = 𝟙 T)
    (hΓ : Function.Surjective π.appTop) : Function.Injective z.appTop := by
  intro r s hrs
  obtain ⟨a, rfl⟩ := hΓ r
  obtain ⟨b, rfl⟩ := hΓ s
  have h (c : Γ(T, ⊤)) : z.appTop (π.appTop c) = c :=
    congrArg (fun f : T ⟶ T ↦ f.appTop c) hπ
  rw [h, h] at hrs
  exact congrArg π.appTop hrs

theorem section_pullbackEnd_injective (hπ : z ≫ π = 𝟙 T)
    (hΓ : Function.Surjective π.appTop) {M : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) :
    Function.Injective (fun q : M ⟶ M ↦ (Scheme.Modules.pullback z).map q) := by
  intro q q' hq
  obtain ⟨r, rfl⟩ := LineEndomorphisms.exists_scalarEnd hM q
  obtain ⟨s, rfl⟩ := LineEndomorphisms.exists_scalarEnd hM q'
  change (Scheme.Modules.pullback z).map (ModuleScalar.scalarEnd M r) =
    (Scheme.Modules.pullback z).map (ModuleScalar.scalarEnd M s) at hq
  rw [ModuleScalar.scalarEnd_pullback, ModuleScalar.scalarEnd_pullback] at hq
  have hr := LineEndomorphisms.scalarEnd_injective (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback z M hM) hq
  exact congrArg (ModuleScalar.scalarEnd M) (section_appTop_injective π z hπ hΓ hr)

theorem iso_eq_of_section (hπ : z ≫ π = 𝟙 T)
    (hΓ : Function.Surjective π.appTop) {M N : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (e f : M ≅ N)
    (hef : (Scheme.Modules.pullback z).map e.hom = (Scheme.Modules.pullback z).map f.hom) :
    e = f := by
  apply Iso.ext
  apply (cancel_mono f.inv).mp
  apply section_pullbackEnd_injective π z hπ hΓ hM
  change (Scheme.Modules.pullback z).map (e.hom ≫ f.inv) =
    (Scheme.Modules.pullback z).map (f.hom ≫ f.inv)
  rw [Functor.map_comp, Functor.map_comp, hef]

theorem normalizedIso_unique (hπ : z ≫ π = 𝟙 T)
    (hΓ : Function.Surjective π.appTop) {M N : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (e f : M ≅ N)
    (he : (Scheme.Modules.pullback z).map e.hom ≫ eN.hom = eM.hom)
    (hf : (Scheme.Modules.pullback z).map f.hom ≫ eN.hom = eM.hom) : e = f := by
  apply iso_eq_of_section π z hπ hΓ hM e f
  exact (cancel_mono eN.hom).mp (he.trans hf.symm)

/-- Every existing isomorphism has exactly one normalized representative. -/
theorem existsUnique_normalizedIso (hπ : z ≫ π = 𝟙 T)
    (hΓ : Function.Surjective π.appTop) {M N : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) (e : M ≅ N) :
    ∃! f : M ≅ N, (Scheme.Modules.pullback z).map f.hom ≫ eN.hom = eM.hom := by
  refine ⟨RigidifiedIso.normalizedIso π z e eM eN, RigidifiedIso.normalizedIso_section π z hπ e eM eN, ?_⟩
  intro f hf
  exact normalizedIso_unique π z hπ hΓ hM eM eN f _ hf
    (RigidifiedIso.normalizedIso_section π z hπ e eM eN)

/-- The scalar-control hypothesis is proved for the actual proper product,
with no reducedness or finite-type restriction on the test scheme. -/
theorem proper_product_normalizedIso_unique
    {k : Type u} [Field k] [IsAlgClosed k]
    (T A : Over (Spec (.of k))) [IsProper A.hom] [IsIntegral A.left]
    (z : T.left ⟶ (T ⊗ A).left) (hz : z ≫ (fst T A).left = 𝟙 T.left)
    {M N : (T ⊗ A).left.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
    (e f : M ≅ N)
    (he : (Scheme.Modules.pullback z).map e.hom ≫ eN.hom = eM.hom)
    (hf : (Scheme.Modules.pullback z).map f.hom ≫ eN.hom = eM.hom) : e = f := by
  have hΓ : IsIso ((fst T A).left.appTop) := ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections.Construction.isIso_properBaseChange_app T A ⊤
  exact normalizedIso_unique (fst T A).left z hz
    (ConcreteCategory.bijective_of_isIso ((fst T A).left.appTop)).surjective hM eM eN e f he hf

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedUniqueness
