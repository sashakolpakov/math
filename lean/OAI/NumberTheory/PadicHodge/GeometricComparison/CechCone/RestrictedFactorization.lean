import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Realization
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartNaturality

/-! # Restricted Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RestrictedFactorization.CechConeRestrictedFactorization

noncomputable section

/-! A section cone factors through the comparison on a fixed local
chart whenever the section functor factors through that restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem chain {D : Type*} [Category D] {A B C E F G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : B ⟶ F)
    (e : F ⟶ E) (f : A ⟶ G) (g : G ⟶ F)
    (hn : b ≫ c = d ≫ e) (hf : a ≫ d = f ≫ g) :
    (a ≫ b) ≫ c = f ≫ (g ≫ e) := by
  rw [Category.assoc, hn, ← Category.assoc, hf, Category.assoc]

universe u a b c d e f g h
variable (C : Type u) [SemilatticeInf C] {ι : Type} [Finite ι]
  (U : ι → C) (V : C)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {E : Type e} [Category.{f} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  {D : Type g} [Category.{h} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (S : A ⥤ B) [S.Additive] (H : B ⥤ D) [H.Additive]
  (F : A ⥤ E) [F.Additive] (T : E ⥤ D) [T.Additive]
  (e : S ⋙ H ≅ F ⋙ T) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (hF : ∀ W : C, IsIso ((F.mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)))

include hF in
omit [HasProducts.{0} A] [HasCoproducts.{0} A] [HasProducts.{0} E] [HasCoproducts.{0} E]
  [HasProducts.{0} D] [HasCoproducts.{0} D] in
theorem right_meet (W : C) : IsIso (((F ⋙ T).mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)) := by
  let := hF W
  exact inferInstanceAs (IsIso ((T.mapHomologicalComplex (.up ℕ)).map
    ((F.mapHomologicalComplex (.up ℕ)).map (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))))

include e hF in
omit [HasProducts.{0} A] [HasCoproducts.{0} A] [HasProducts.{0} B] [HasCoproducts.{0} B]
  [HasProducts.{0} E] [HasCoproducts.{0} E] [HasProducts.{0} D] [HasCoproducts.{0} D] in
theorem left_meet (W : C) : IsIso (((S ⋙ H).mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)) :=
  (NatIso.isIso_map_iff (NatIso.mapHomologicalComplex e (.up ℕ))
    (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)).mpr
      (right_meet C V F T P hF W)

variable (M : CochainComplex B ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ TotalCoefficient.CechConeTotalCoefficient.mapped S P)

theorem factorization :
    (H.mapHomologicalComplex (.up ℕ)).map (Realization.CechConeRealization.map S U P M η) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (Total.CechConeTotal.total U P)).hom =
      ((H.mapHomologicalComplex (.up ℕ)).map (η.app (op V)) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op V))).hom) ≫
          (T.mapHomologicalComplex (.up ℕ)).map (Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF) := by
  rw [Realization.CechConeRealization.coefficients]
  let θ := TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone H
    (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η
  have hf := Semilattice.MappedChartNaturality.SemilatticeMappedChartNaturality.cone_factorization C U V (S ⋙ H) P
    (left_meet C V S H F T e P hF) ((H.mapHomologicalComplex (.up ℕ)).obj M) θ
  change Realization.CechConeRealization.map (S ⋙ H) U P ((H.mapHomologicalComplex (.up ℕ)).obj M) θ ≫ _ = _
  rw [show Realization.CechConeRealization.map (S ⋙ H) U P ((H.mapHomologicalComplex (.up ℕ)).obj M) θ =
      θ.app (op V) ≫ Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map C U V (S ⋙ H) P
        (left_meet C V S H F T e P hF) from hf]
  rw [Category.assoc, Semilattice.MappedChartNaturality.SemilatticeMappedChartNaturality.iso C U V (S ⋙ H) P
    (left_meet C V S H F T e P hF) (F ⋙ T) e (right_meet C V F T P hF),
    ← Semilattice.MappedChartNaturality.SemilatticeMappedChartNaturality.composition C U V F P hF T (right_meet C V F T P hF)]
  change (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone H
    (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η).app (op V) ≫ _ = _
  rw [TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  exact (Category.assoc _ _ _).symm

theorem comparison {K : CochainComplex A ℕ} (b : Total.CechConeTotal.total U P ⟶ K) :
    (H.mapHomologicalComplex (.up ℕ)).map
        (Realization.CechConeRealization.map S U P M η ≫ (S.mapHomologicalComplex (.up ℕ)).map b) ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom =
    ((H.mapHomologicalComplex (.up ℕ)).map (η.app (op V)) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op V))).hom) ≫
      (T.mapHomologicalComplex (.up ℕ)).map
        (Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF ≫ (F.mapHomologicalComplex (.up ℕ)).map b) := by
  have hn := (NatIso.mapHomologicalComplex e (.up ℕ)).hom.naturality b
  have hf := factorization C U V S H F T e P hF M η
  have hc := chain _ _ _ _ _ _ _ hn hf
  exact (congrArg (fun q => q ≫ ((NatIso.mapHomologicalComplex e (.up ℕ)).app K).hom)
    ((H.mapHomologicalComplex (.up ℕ)).map_comp (Realization.CechConeRealization.map S U P M η)
      ((S.mapHomologicalComplex (.up ℕ)).map b))).trans
    (hc.trans (congrArg (fun q => ((H.mapHomologicalComplex (.up ℕ)).map (η.app (op V)) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op V))).hom) ≫ q)
      ((T.mapHomologicalComplex (.up ℕ)).map_comp
        (Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF)
        ((F.mapHomologicalComplex (.up ℕ)).map b)).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RestrictedFactorization.CechConeRestrictedFactorization
