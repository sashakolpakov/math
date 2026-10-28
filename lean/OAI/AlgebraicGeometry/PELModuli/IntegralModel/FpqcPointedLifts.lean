import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PointedLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs

/-! # Fpqc Pointed Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FpqcPointedLifts.PointedLiftParameters

noncomputable section

/-! Effective descent of a specified pointed unramified lift through an
fpqc base cover. Relative uniqueness proves the overlap equation, and the
actual morphism descends as a coequalizer. No Hom representation is supplied. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme} (X Y Z : Over S) (q : Y ⟶ Z) (b : X ⟶ Z)
  (x₀ : ⊤_ (Over S) ⟶ X) (y₀ : ⊤_ (Over S) ⟶ Y)
  [GeometricallyConnected X.hom] [FormallyUnramified q.left]
  [LocallyOfFiniteType q.left] [IsSeparated q.left]

theorem unique_on_geometric_source {T : Over S} (f g : T ⨯ X ⟶ Y)
    (hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f) (hg : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ g) : f = g := by
  have hp : GeometricallyConnected (prod.fst : T ⨯ X ⟶ T).left := by
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T X)).flip
      (inferInstanceAs (GeometricallyConnected X.hom))
  have hs : (PointedLift.PointedLiftParameters.sectionAt X x₀ T).left ≫ (prod.fst : T ⨯ X ⟶ T).left = 𝟙 T.left :=
    congrArg Over.Hom.left (prod.lift_fst _ _)
  apply Over.OverMorphism.ext
  exact Relative.PointedLifts.relative_pointed_unramified_lifts_unique (prod.fst : T ⨯ X ⟶ T).left
    (PointedLift.PointedLiftParameters.sectionAt X x₀ T).left hs q.left f.left g.left
    (congrArg Over.Hom.left (hf.1.trans hg.1.symm))
    (congrArg Over.Hom.left (hf.2.trans hg.2.symm))

/-- Relative uniqueness supplies the descent datum of the specified lift.
The descended map and both pointed-lift equations are constructed over S. -/
theorem fpqc_pointed_lift_descends
    (T : Over S) [Flat T.hom] [Surjective T.hom] [QuasiCompact T.hom]
    (f : T ⨯ X ⟶ Y) (hf : PointedLift.PointedLiftParameters.IsPointedLift X Y Z q b x₀ y₀ f) :
    ∃! r : X ⟶ Y, r ≫ q = b ∧ x₀ ≫ r = y₀ ∧ prod.snd ≫ r = f := by
  let π : T ⨯ X ⟶ X := prod.snd
  have : Flat π.left := by rw [← Over.prodLeftIsoPullback_hom_snd]; infer_instance
  have : Surjective π.left := by rw [← Over.prodLeftIsoPullback_hom_snd]; infer_instance
  have : QuasiCompact π.left := by rw [← Over.prodLeftIsoPullback_hom_snd]; infer_instance
  have : EffectiveEpi π := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc π
  have hdouble : prod.map (prod.fst : T ⨯ T ⟶ T) (𝟙 X) ≫ f =
      prod.map (prod.snd : T ⨯ T ⟶ T) (𝟙 X) ≫ f :=
    unique_on_geometric_source X Y Z q b x₀ y₀ _ _
      (PointedLift.PointedLiftParameters.isPointedLift_restrict X Y Z q b x₀ y₀ prod.fst f hf)
      (PointedLift.PointedLiftParameters.isPointedLift_restrict X Y Z q b x₀ y₀ prod.snd f hf)
  have hcoeq : ∀ {W : Over S} (a c : W ⟶ T ⨯ X), a ≫ π = c ≫ π → a ≫ f = c ≫ f := by
    intro W a c hac
    let l : W ⟶ (T ⨯ T) ⨯ X :=
      prod.lift (prod.lift (a ≫ prod.fst) (c ≫ prod.fst)) (a ≫ prod.snd)
    have hl₁ : l ≫ prod.map (prod.fst : T ⨯ T ⟶ T) (𝟙 X) = a := by
      apply prod.hom_ext <;> simp only [l, Category.assoc, prod.map_fst, prod.map_snd,
        prod.lift_fst_assoc, prod.lift_fst, prod.lift_snd, Category.comp_id]
    have hl₂ : l ≫ prod.map (prod.snd : T ⨯ T ⟶ T) (𝟙 X) = c := by
      apply prod.hom_ext
      · simp only [l, Category.assoc, prod.map_fst, prod.lift_fst_assoc, prod.lift_snd]
      · simpa only [l, Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd] using hac
    have h := congrArg (fun m => l ≫ m) hdouble
    rw [← Category.assoc, hl₁, ← Category.assoc, hl₂] at h
    exact h
  let r := EffectiveEpi.desc π f hcoeq
  have hr : π ≫ r = f := EffectiveEpi.fac _ _ _
  have hq : r ≫ q = b := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hr]
    exact hf.1
  let t : T ⟶ ⊤_ (Over S) := terminal.from T
  let e : ⊤_ (Over S) ≅ Over.mk (𝟙 S) := terminalIsoIsTerminal Over.mkIdTerminal
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have ht : t.left ≫ e.hom.left = T.hom := by
    simpa only [Over.comp_left, Over.mk_left, Over.mk_hom, Category.comp_id] using
      (Over.w (t ≫ e.hom))
  have : IsIso e.inv.left := ((Over.forget S).mapIso e).isIso_inv
  have ht' : t.left = T.hom ≫ e.inv.left := by
    rw [← ht, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left,
      Category.comp_id]
  have : Flat t.left := by rw [ht']; infer_instance
  have : Surjective t.left := by rw [ht']; infer_instance
  have : QuasiCompact t.left := by rw [ht']; infer_instance
  have : EffectiveEpi t := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc t
  have hp : x₀ ≫ r = y₀ := by
    apply (cancel_epi t).mp
    calc
      t ≫ (x₀ ≫ r) = (PointedLift.PointedLiftParameters.sectionAt X x₀ T ≫ π) ≫ r := by
        rw [PointedLift.PointedLiftParameters.sectionAt, prod.lift_snd, Category.assoc]
      _ = PointedLift.PointedLiftParameters.sectionAt X x₀ T ≫ f := by rw [Category.assoc, hr]
      _ = t ≫ y₀ := hf.2
  exact ⟨r, ⟨hq, hp, hr⟩, fun a ha => (cancel_epi π).mp (ha.2.2.trans hr.symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FpqcPointedLifts.PointedLiftParameters
