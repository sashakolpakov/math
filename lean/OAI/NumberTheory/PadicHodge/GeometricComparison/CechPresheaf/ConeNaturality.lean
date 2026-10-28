import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Cone Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality

noncomputable section

/-! A commuting map of actual presheaf-complex cones preserves the
canonical edge into the original Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
universe u v a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ} {M N : CochainComplex A ℕ}
  (η : (ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K) (θ : (ConeTotal.CechPresheafConeTotal.constant (C := C)).obj N ⟶ L)
  (α : K ⟶ L) (β : M ⟶ N) (h : η ≫ α = (ConeTotal.CechPresheafConeTotal.constant (C := C)).map β ≫ θ)

local instance cech_additive : (IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).Additive
  infer_instance

def bicomplexMap : ConeTotal.CechPresheafConeTotal.bicomplex U K ⟶ ConeTotal.CechPresheafConeTotal.bicomplex U L :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map α

local instance hasTotal (B : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : B.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def totalMap : (ConeTotal.CechPresheafConeTotal.bicomplex U K).total (.up ℕ) ⟶ (ConeTotal.CechPresheafConeTotal.bicomplex U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U α) (.up ℕ)

include h in
omit [HasCoproducts.{0} A] in
theorem component_naturality (q : ℕ) : ConeTotal.CechPresheafConeTotal.component U K M η q ≫ ((bicomplexMap U α).f q).f 0 =
    β.f q ≫ ConeTotal.CechPresheafConeTotal.component U L N θ q := by
  change Pi.lift (fun t : Fin 1 → ι => (η.f q).app (op (∏ᶜ (U ∘ t)))) ≫
      Limits.Pi.map (fun t : Fin 1 → ι => (α.f q).app (op (∏ᶜ (U ∘ t)))) =
    β.f q ≫ Pi.lift (fun t : Fin 1 → ι => (θ.f q).app (op (∏ᶜ (U ∘ t))))
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.map_π]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
  exact congrArg (fun γ => (γ.f q).app (op (∏ᶜ (U ∘ t)))) h

include h in
omit [HasCoproducts.{0} A] in
theorem naturality : ConeTotal.CechPresheafConeTotal.map U K M η ≫ totalMap U α = β ≫ ConeTotal.CechPresheafConeTotal.map U L N θ := by
  apply HomologicalComplex.Hom.ext
  funext q
  let B := ConeTotal.CechPresheafConeTotal.bicomplex U K
  let D := ConeTotal.CechPresheafConeTotal.bicomplex U L
  let a := bicomplexMap U α
  change (ConeTotal.CechPresheafConeTotal.component U K M η q ≫ B.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    β.f q ≫ ConeTotal.CechPresheafConeTotal.component U L N θ q ≫ D.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => ConeTotal.CechPresheafConeTotal.component U K M η q ≫ k)
      (HomologicalComplex₂.ιTotal_map B D a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ D.ιTotal (.up ℕ) q 0 q rfl)
            (component_naturality U η θ α β h q)).trans (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality
