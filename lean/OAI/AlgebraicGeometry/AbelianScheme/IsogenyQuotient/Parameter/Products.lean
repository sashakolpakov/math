import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupRepresentable

/-! # Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Products.Construction

noncomputable section

/-!
Finite products of the chosen-block parameter schemes. Tuple choices are
encoded recursively by nested pairs; this records one subgroup choice for
each member of Fin s, with no independence or product-representability axiom.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}}

def pairChoiceFunctor (F G : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := F.obj T × G.obj T
  map f := ↾fun x => (F.map f x.1, G.map f x.2)
  map_id _ := by ext x <;> simp
  map_comp _ _ := by ext x <;> simp

def pairChoices_representable
    (F G : (Over S)ᵒᵖ ⥤ Type (u + 1)) {P Q : Over S}
    (eF : F.RepresentableBy P) (eG : G.RepresentableBy Q) :
    (pairChoiceFunctor F G).RepresentableBy (P ⊗ Q) where
  homEquiv := {
    toFun x := (eF.homEquiv (x ≫ fst P Q), eG.homEquiv (x ≫ snd P Q))
    invFun x := lift (eF.homEquiv.symm x.1) (eG.homEquiv.symm x.2)
    left_inv x := by simp
    right_inv x := by
      cases x
      simp
      rfl
  }
  homEquiv_comp f g := by
    change (eF.homEquiv ((f ≫ g) ≫ fst P Q), eG.homEquiv ((f ≫ g) ≫ snd P Q)) = _
    simp only [Category.assoc, eF.homEquiv_comp, eG.homEquiv_comp]
    rfl

theorem finite_etale_pair_parameters
    (F G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : ∃ P : Over S, IsFinite P.hom ∧ Etale P.hom ∧ Nonempty (F.RepresentableBy P))
    (hG : ∃ Q : Over S, IsFinite Q.hom ∧ Etale Q.hom ∧ Nonempty (G.RepresentableBy Q)) :
    ∃ R : Over S,
      IsFinite R.hom ∧ Etale R.hom ∧ Nonempty ((pairChoiceFunctor F G).RepresentableBy R) := by
  obtain ⟨P, hPfinite, hPetale, ⟨eP⟩⟩ := hF
  obtain ⟨Q, hQfinite, hQetale, ⟨eQ⟩⟩ := hG
  have : IsFinite P.hom := hPfinite
  have : Etale P.hom := hPetale
  have : IsFinite Q.hom := hQfinite
  have : Etale Q.hom := hQetale
  refine ⟨P ⊗ Q, ?_, ?_, ⟨pairChoices_representable F G eP eQ⟩⟩
  · change IsFinite (pullback.fst P.hom Q.hom ≫ P.hom)
    infer_instance
  · change Etale (pullback.fst P.hom Q.hom ≫ P.hom)
    infer_instance

def emptyChoiceFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Functor.const (Over S)ᵒᵖ).obj PUnit.{u + 2}

def emptyChoices_representable :
    (emptyChoiceFunctor (S := S)).RepresentableBy (Over.mk (𝟙 S)) where
  homEquiv := {
    toFun _ := PUnit.unit
    invFun _ := Over.homMk _ rfl
    left_inv x := by
      apply Over.OverMorphism.ext
      exact x.w.symm.trans (Category.comp_id x.left)
    right_inv x := by
      change PUnit.unit = x
      cases x
      rfl
  }
  homEquiv_comp _ _ := rfl

def blockTupleFunctor : (s : ℕ) → (Fin s → (Over S)ᵒᵖ ⥤ Type (u + 1)) →
    (Over S)ᵒᵖ ⥤ Type (u + 1)
  | 0, _ => emptyChoiceFunctor
  | s + 1, F => pairChoiceFunctor (F 0) (blockTupleFunctor s (fun i => F i.succ))

theorem finite_etale_block_tuples
    (s : ℕ) (F : Fin s → (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : ∀ i, ∃ P : Over S,
      IsFinite P.hom ∧ Etale P.hom ∧ Nonempty ((F i).RepresentableBy P)) :
    ∃ P : Over S,
      IsFinite P.hom ∧ Etale P.hom ∧ Nonempty ((Construction.blockTupleFunctor s F).RepresentableBy P) := by
  induction s with
  | zero =>
      refine ⟨Over.mk (𝟙 S), ?_, ?_, ⟨emptyChoices_representable⟩⟩
      · change IsFinite (𝟙 S)
        infer_instance
      · change Etale (𝟙 S)
        infer_instance
  | succ s ih =>
      exact finite_etale_pair_parameters (F 0) (Construction.blockTupleFunctor s (fun i => F i.succ))
        (hF 0) (ih _ (fun i => hF i.succ))

open scoped _root_.CategoryTheory.MonObj in
/-- The parameter space for all chosen blocks is finite etale over the
source moduli, using the complete repaired TorsionQuotient proposition explicitly. -/
theorem chosen_block_parameters_from_TorsionQuotient
    {K : Type u} [Field K] [CharZero K] (base : S ⟶ Spec (CommRingCat.of K))
    (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (hn : 0 < n) (s : ℕ)
    (M : Fin s → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (projectorLift : Fin s → (A ⟶ A)) [∀ i, IsMonHom (projectorLift i)]
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) :
    ∃ P : Over S,
      IsFinite P.hom ∧ Etale P.hom ∧
      Nonempty ((Construction.blockTupleFunctor s (fun i =>
        SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (projectorLift i))).RepresentableBy P) := by
  apply finite_etale_block_tuples
  intro i
  exact SubgroupRepresentable.Construction.finite_etale_supported_subgroups_of_TorsionQuotient n (M i) (projectorLift i)
    (h_TorsionQuotient A n hn (Unit.Construction.positive_integer_unit_on_characteristic_zero_base base n hn) (M i))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Products.Construction
