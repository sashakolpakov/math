import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Kernel Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.KernelQuotient.Construction

noncomputable section

/-!
The universal finite-etale source parameter and its quotient isogeny are
constructed together from TorsionQuotient and FiniteDescent. The full kernel is the canonical
one defined from chosen subgroups and opposite annihilators; its geometric
model is produced by the proof. Polarization and the moduli target are
subsequent steps and are not premises of this construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}}

/-- The complete universal kernel-and-isogeny geometry. This proposition
contains the constructed parameter and model as existential conclusions. -/
def UniversalKernelQuotient
    (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (n s : ℕ)
    (M : Fin s → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p q : Fin s → (A.toOver ⟶ A.toOver)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over S} [GrpObj W]
    (pairing : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i))
      (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W)) : Prop :=
    ∃ P : Over S, IsFinite P.hom ∧ Etale P.hom ∧
      ∃ repr : (Parameter.Products.Construction.blockTupleFunctor s (fun i =>
        SubgroupFunctor.Construction.supportedSubgroupFunctor A.toOver n (M i) (p i))).RepresentableBy P,
      let U := Choices.Construction.universalBlockChoice n s M p repr
      let F := ChoiceKernel.Construction.choiceFullKernel n s M p q pairing U
      ∃ R : F.Model,
      ∃ (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left)
        (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (IsogenyComplement.Construction.baseChangedAbelianScheme A P) B)
        (g : B.toOver ⟶ (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver),
        Etale f.hom.left ∧ IsMonHom g ∧
        f.hom ≫ g = (𝟙 (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver) ^ n ∧
        g ≫ f.hom = (𝟙 B.toOver) ^ n ∧
        (∀ (T : Over P.left) (a : T ⟶ (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver),
          a ≫ f.hom = 1 ↔ ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
            h ≫ (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom = a) ∧
        Descent.Construction.QuotientUniversalProperty (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f.hom

theorem universal_quotient_from_TorsionQuotient_FiniteDescent
    {K : Type u} [Field K] [CharZero K] (base : S ⟶ Spec (.of K))
    (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (n : ℕ) (hn : 0 < n) (s : ℕ)
    (M : Fin s → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p q : Fin s → (A.toOver ⟶ A.toOver)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over S} [GrpObj W] [Etale W.hom] [IsSeparated W.hom]
    (pairing : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i))
      (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
    (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p q j) ≫
        Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p q i) = 1)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{u}) :
    UniversalKernelQuotient A n s M p q pairing := by
  obtain ⟨P, hPfinite, hPetale, ⟨repr⟩⟩ := Parameter.Products.Construction.chosen_block_parameters_from_TorsionQuotient
    base A.toOver n hn s M p h_TorsionQuotient
  let U := Choices.Construction.universalBlockChoice n s M p repr
  let F := ChoiceKernel.Construction.choiceFullKernel n s M p q pairing U
  have htor := Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.toOver) base n hn h_TorsionQuotient
  let R := ChoiceKernel.Construction.choiceFullKernel_model n s M p q pairing U hsep htor
  have hFkilled : F.KilledBy n := ChoiceKernel.Construction.choiceFullKernel_killed n s M p q pairing U
  obtain ⟨B, f, g, hg, hfg, hgf, hker, hUP⟩ :=
    IsogenyComplement.Construction.quotient_isogeny_and_complement_of_FiniteDescent A P F R n hFkilled h_FiniteDescent
  refine ⟨P, hPfinite, hPetale, repr, R, B, f, g, ?_, hg, hfg, hgf, hker, hUP⟩
  exact IsogenyQuotient.Etale.Construction.constructed_quotient_etale A P F R n hFkilled htor.2 B f hker

theorem classified_full_kernel_is_pullback
    {A : Over S} [GrpObj A] [IsCommMonObj A]
    (n s : ℕ) (M : Fin s → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p q : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over S} [GrpObj W]
    (pairing : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i))
      (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
    {P T : Over S}
    (repr : (Parameter.Products.Construction.blockTupleFunctor s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i))).RepresentableBy P)
    (b : T ⟶ P) :
    ChoiceKernel.Construction.choiceFullKernel n s M p q pairing
      (Choices.Construction.blockTupleCoordinates s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) (.op T)
        (repr.homEquiv b)) =
      (ChoiceKernel.Construction.choiceFullKernel n s M p q pairing (Choices.Construction.universalBlockChoice n s M p repr)).baseChange b := by
  have hU : Choices.Construction.blockTupleCoordinates s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) (.op T)
      (repr.homEquiv b) = ChoiceKernel.Construction.blockChoicesBaseChange n s M p (Choices.Construction.universalBlockChoice n s M p repr) b := by
    funext i
    exact Choices.Construction.represented_block_coordinates s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) repr b i
  rw [hU, ChoiceKernel.Construction.choiceFullKernel_baseChange]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.KernelQuotient.Construction
