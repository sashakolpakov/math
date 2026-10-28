import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Component Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The supplied finite component decomposition covers the actual
geometric reduction, and each of its images is connected. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

def Models.RankThreePELModel.GoodIntegralReduction.geometricComponent (a : M.Family) (t : Fin (M.componentCount a)) :
    Over (Spec (.of (AlgebraicClosure (ZMod q)))) :=
  (Over.pullback R.geometricBase).obj ((M.components a).S t)

def Models.RankThreePELModel.GoodIntegralReduction.geometricComponentInclusion (a : M.Family) (t : Fin (M.componentCount a)) :
    R.geometricComponent a t ⟶ R.geometricFiber a :=
  (Over.pullback R.geometricBase).map
    (Sigma.ι (M.components a).S t ≫ (M.decomposition a).hom)

theorem Models.RankThreePELModel.GoodIntegralReduction.geometricComponent_connected (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) :
    ConnectedSpace (R.geometricComponent a t).left := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc⟩ := hM.2.2 a
  let : GeometricallyConnected ((M.components a).S t).hom := (hc t).2.2.2
  exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace
    (AlgebraicClosure (ZMod q)) R.geometricBase

theorem Models.RankThreePELModel.GoodIntegralReduction.geometricComponent_cover (a : M.Family) (x : R.geom a) :
    ∃ t, x ∈ Set.range (R.geometricComponentInclusion a t).left :=
  IntegralModel.Coproduct.baseChange_decomposition_cover (M.components a).S R.geometricBase
    (M.decomposition a) x

theorem Models.RankThreePELModel.GoodIntegralReduction.geometricComponent_range_subset (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) (x : R.geom a)
    (hx : x ∈ Set.range (R.geometricComponentInclusion a t).left) :
    Set.range (R.geometricComponentInclusion a t).left ⊆ connectedComponent x := by
  let : ConnectedSpace (R.geometricComponent a t).left := R.geometricComponent_connected hM a t
  exact (isConnected_range (R.geometricComponentInclusion a t).left.continuous).subset_connectedComponent hx

/-- A finite list of constructed ordinary points supplies an ordinary
point in every connected component. This is a reduction lemma, not an
existence assumption in the CMPoints statement. -/
theorem Models.RankThreePELModel.GoodIntegralReduction.ordinary_point_in_component_of_finite_points (hM : M.HasPrescribedBallPeriods)
    (a : M.Family)
    (y : ∀ t : Fin (M.componentCount a), (R.geometricComponent a t).left)
    (hy : ∀ t, R.IsOrdinary a ((R.geometricComponentInclusion a t).left (y t)))
    (x : R.geom a) : ∃ z : connectedComponent x, R.IsOrdinary a z.val := by
  obtain ⟨t, ht⟩ := R.geometricComponent_cover a x
  exact ⟨⟨(R.geometricComponentInclusion a t).left (y t),
    R.geometricComponent_range_subset hM a t x ht (Set.mem_range_self _)⟩, hy t⟩

/-- Specialization takes place on the chosen component itself. -/
def Models.RankThreePELModel.GoodIntegralReduction.componentGeometricPointOfIntegral (a : M.Family) (t : Fin (M.componentCount a))
    (z : Spec (.of (PadicInt q)) ⟶ ((M.components a).S t).left)
    (hz : z ≫ ((M.components a).S t).hom = R.integralBasePoint) :
    Spec (.of (AlgebraicClosure (ZMod q))) ⟶ (R.geometricComponent a t).left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) ≫
      Spec.map (CommRingCat.ofHom (PadicInt.toZMod : PadicInt q →+* ZMod q)) ≫ z)
    (𝟙 _) (by
      rw [Category.assoc, Category.assoc, hz, R.integralBasePoint_residue,
        Category.id_comp, R.geometricBase_factors])

theorem Models.RankThreePELModel.GoodIntegralReduction.componentGeometricPointOfIntegral_inclusion
    (a : M.Family) (t : Fin (M.componentCount a))
    (z : Spec (.of (PadicInt q)) ⟶ ((M.components a).S t).left)
    (hz : z ≫ ((M.components a).S t).hom = R.integralBasePoint) :
    R.componentGeometricPointOfIntegral a t z hz ≫ (R.geometricComponentInclusion a t).left =
      R.geometricPointOfIntegral a
        (z ≫ (Sigma.ι (M.components a).S t ≫ (M.decomposition a).hom).left)
        (by rw [Category.assoc, Over.w]; exact hz) := by
  dsimp only [Models.RankThreePELModel.GoodIntegralReduction.geometricComponent, Models.RankThreePELModel.GoodIntegralReduction.geometricFiber, Models.RankThreePELModel.GoodIntegralReduction.geom]
  apply pullback.hom_ext
  · simp only [Models.RankThreePELModel.GoodIntegralReduction.geometricComponentInclusion, Over.pullback_map_left,
      Models.RankThreePELModel.GoodIntegralReduction.componentGeometricPointOfIntegral, Models.RankThreePELModel.GoodIntegralReduction.geometricPointOfIntegral]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Models.RankThreePELModel.GoodIntegralReduction.geometricComponentInclusion, Over.pullback_map_left,
      Models.RankThreePELModel.GoodIntegralReduction.componentGeometricPointOfIntegral, Models.RankThreePELModel.GoodIntegralReduction.geometricPointOfIntegral]
    simp only [Category.assoc, pullback.lift_snd]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
