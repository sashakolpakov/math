import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Cone Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal

noncomputable section

/-! A cone into an actual presheaf complex gives the canonical edge
map to its original Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)

local instance cech_additive : (IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).Additive
  infer_instance

def constant : CochainComplex A ℕ ⥤ CochainComplex (Cᵒᵖ ⥤ A) ℕ :=
  (Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)

def bicomplex (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ) : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).obj K

variable (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (M : CochainComplex A ℕ)
  (η : (constant (C := C)).obj M ⟶ K)

def component (q : ℕ) : M.X q ⟶ ((CechPresheafConeTotal.bicomplex U K).X q).X 0 :=
  (NonemptyCech.Augmentation.NonemptyCechAugmentation.restriction U (K.X q) (M.X q) (η.f q)).app ⦋0⦌

omit [HasCoproducts.{0} A] in
theorem comm (q q' : ℕ) : component U K M η q ≫ ((CechPresheafConeTotal.bicomplex U K).d q q').f 0 =
    M.d q q' ≫ component U K M η q' := by
  change Pi.lift (fun t : Fin 1 → ι => (η.f q).app (op (∏ᶜ (U ∘ t)))) ≫
      Limits.Pi.map (fun t : Fin 1 → ι => (K.d q q').app (op (∏ᶜ (U ∘ t)))) =
    M.d q q' ≫ Pi.lift (fun t : Fin 1 → ι => (η.f q').app (op (∏ᶜ (U ∘ t))))
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.map_π]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
  exact congrArg (fun α => α.app (op (∏ᶜ (U ∘ t)))) (η.comm q q')

omit [HasCoproducts.{0} A] in
theorem cocycle (q : ℕ) : component U K M η q ≫ ((CechPresheafConeTotal.bicomplex U K).X q).d 0 1 = 0 :=
  NonemptyCech.Augmentation.NonemptyCechAugmentation.cocycle U (K.X q) (M.X q) (η.f q)

local instance hasTotal : (CechPresheafConeTotal.bicomplex U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def map : M ⟶ (CechPresheafConeTotal.bicomplex U K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex U K)) M (component U K M η)
    (fun q q' _ => CechPresheafConeTotal.comm U K M η q q') (cocycle U K M η)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
