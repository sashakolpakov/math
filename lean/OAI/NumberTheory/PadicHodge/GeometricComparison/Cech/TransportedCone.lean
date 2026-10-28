import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality

/-! # Transported Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TransportedCone.CechTransportedCone

noncomputable section

/-! Transport a global cone through the original section-coordinate
isomorphisms, retaining each of those isomorphisms in the comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

local notation "H" => Functor.mapHomologicalComplex
  (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F) (ComplexShape.up ℕ)

variable {P Q : CochainComplex (Dᵒᵖ ⥤ A) ℕ}
  {N : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (e₀ : N ≅
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F).mapHomologicalComplex (.up ℕ)).obj Q)
  (e₁ : P ≅ Q) (M : CochainComplex A ℕ) (η : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := D)).obj M ⟶ P)

def cone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ N :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F Q M (η ≫ e₁.hom) ≫ e₀.inv

def edge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U N M (cone F e₀ e₁ M η)

def bicomplexIso : CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U N ≅ CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (F.obj ∘ U) P :=
  ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).mapIso e₀ ≪≫
    NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U Q ≪≫
    ((IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U)).mapHomologicalComplex (.up ℕ)).mapIso e₁.symm

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D]
  [HasProducts A] [HasCoproducts A] in
theorem first_square : cone F e₀ e₁ M η ≫ e₀.hom =
    (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).map (𝟙 M) ≫ CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F Q M (η ≫ e₁.hom) := by
  rw [(CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).map_id]
  simp only [cone, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

omit [Quiver.IsThin D] [HasBinaryProducts D] [HasProducts A] [HasCoproducts A] in
theorem last_square : (η ≫ e₁.hom) ≫ e₁.inv = (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := D)).map (𝟙 M) ≫ η := by
  rw [(CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := D)).map_id]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

omit [Quiver.IsThin D] [HasBinaryProducts D] [HasCoproducts A]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F] in
theorem first_edge : edge F U e₀ e₁ M η ≫ CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U e₀.hom =
    CechPresheaf.ConeTotal.CechPresheafConeTotal.map U ((H).obj Q) M (CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F Q M (η ≫ e₁.hom)) :=
  (CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality U (cone F e₀ e₁ M η)
    (CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F Q M (η ≫ e₁.hom)) e₀.hom (𝟙 M)
    (first_square F e₀ e₁ M η)).trans (Category.id_comp _)

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasCoproducts A]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F] in
theorem last_edge : CechPresheaf.ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) Q M (η ≫ e₁.hom) ≫
    CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap (F.obj ∘ U) e₁.inv = CechPresheaf.ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) P M η :=
  (CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality (F.obj ∘ U) (η ≫ e₁.hom) η e₁.inv (𝟙 M)
    (last_square e₁ M η)).trans (Category.id_comp _)

theorem total_coordinates :
    (HomologicalComplex₂.total.mapIso (bicomplexIso F U e₀ e₁) (.up ℕ)).hom =
      CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U e₀.hom ≫
        (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U Q) (.up ℕ)).hom ≫
        CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap (F.obj ∘ U) e₁.inv :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).trans
    (congrArg (fun x => CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U e₀.hom ≫ x)
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

theorem edge_comparison : edge F U e₀ e₁ M η ≫
    (HomologicalComplex₂.total.mapIso (bicomplexIso F U e₀ e₁) (.up ℕ)).hom =
      CechPresheaf.ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) P M η := by
  let a := CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U e₀.hom
  let b := (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U Q) (.up ℕ)).hom
  let c := CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap (F.obj ∘ U) e₁.inv
  let j := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U ((H).obj Q) M (CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F Q M (η ≫ e₁.hom))
  let k := CechPresheaf.ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) Q M (η ≫ e₁.hom)
  have h₁ : edge F U e₀ e₁ M η ≫ a = j := first_edge F U e₀ e₁ M η
  have h₂ : j ≫ b = k := CechPresheaf.ConeProduct.CechPresheafConeProduct.augmentation F U Q M (η ≫ e₁.hom)
  have h₃ : k ≫ c = CechPresheaf.ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) P M η := last_edge F U e₁ M η
  exact (congrArg (fun x => edge F U e₀ e₁ M η ≫ x) (total_coordinates F U e₀ e₁)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ b ≫ c) h₁).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun x => x ≫ c) h₂).trans h₃))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TransportedCone.CechTransportedCone
