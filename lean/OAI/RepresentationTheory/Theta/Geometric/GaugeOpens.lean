import OAI.RepresentationTheory.Theta.Geometric.IsoGaugeCompatibility

/-! # Gauge Opens -/

namespace OAI.RepresentationTheory.Theta.Geometric.GaugeOpens

noncomputable section

section

/-! The coordinate domains for a translation comparison form an actual
open cover and are invariant under the original period lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem thetaFamily_exists_nonzero_coordinate (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (z : Φ.space) :
    ∃ i, F.coordinate i z ≠ 0 := by
  obtain ⟨s, hs, hsz⟩ := F.nonzero z
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  exact ⟨i, hi.symm ▸ hsz⟩

variable (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (a : Φ.space)

def thetaTranslationGaugeOpen
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) : Set Φ.space :=
  {z | (F.coordinate i.1.1 (z + a) ≠ 0 ∧ G.coordinate i.1.2 (z + a) ≠ 0) ∧
    (F.coordinate i.2.1 z ≠ 0 ∧ G.coordinate i.2.2 z ≠ 0)}

theorem thetaTranslationGaugeOpen_isOpen
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) :
    IsOpen (thetaTranslationGaugeOpen F G a i) :=
  ((isOpen_ne_fun ((F.coordinate i.1.1).continuous.comp (continuous_id.add_const a)) continuous_const).inter
    (isOpen_ne_fun ((G.coordinate i.1.2).continuous.comp (continuous_id.add_const a)) continuous_const)).inter
    ((isOpen_ne_fun (F.coordinate i.2.1).continuous continuous_const).inter
      (isOpen_ne_fun (G.coordinate i.2.2).continuous continuous_const))

theorem thetaTranslationGaugeOpen_cover (z : Φ.space) :
    ∃ i, z ∈ thetaTranslationGaugeOpen F G a i := by
  obtain ⟨i, hi⟩ := thetaFamily_exists_nonzero_coordinate F (z + a)
  obtain ⟨j, hj⟩ := thetaFamily_exists_nonzero_coordinate G (z + a)
  obtain ⟨k, hk⟩ := thetaFamily_exists_nonzero_coordinate F z
  obtain ⟨l, hl⟩ := thetaFamily_exists_nonzero_coordinate G z
  exact ⟨((i, j), (k, l)), ⟨hi, hj⟩, ⟨hk, hl⟩⟩

theorem thetaTranslationGaugeOpen_translates
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (l : Φ.periodIntegerLattice) (z : Φ.space) :
    z + l.val ∈ thetaTranslationGaugeOpen F G a i ↔ z ∈ thetaTranslationGaugeOpen F G a i := by
  have hza : z + l.val + a = (z + a) + l.val := by abel
  simp only [thetaTranslationGaugeOpen, Set.mem_ofPred_eq, hza,
    (F.coordinate i.1.1).translates, (G.coordinate i.1.2).translates,
    (F.coordinate i.2.1).translates, (G.coordinate i.2.2).translates,
    mul_ne_zero_iff]
  have hSF : J.value l (z + a) ^ F.degree ≠ 0 := pow_ne_zero _ (J.value_ne_zero l (z + a))
  have hSG : J.value l (z + a) ^ G.degree ≠ 0 := pow_ne_zero _ (J.value_ne_zero l (z + a))
  have hTF : J.value l z ^ F.degree ≠ 0 := pow_ne_zero _ (J.value_ne_zero l z)
  have hTG : J.value l z ^ G.degree ≠ 0 := pow_ne_zero _ (J.value_ne_zero l z)
  exact ⟨fun h => ⟨⟨h.1.1.2, h.1.2.2⟩, ⟨h.2.1.2, h.2.2.2⟩⟩,
    fun h => ⟨⟨⟨hSF, h.1.1⟩, ⟨hSG, h.1.2⟩⟩, ⟨⟨hTF, h.2.1⟩, ⟨hTG, h.2.2⟩⟩⟩⟩

end

/-! The original nonzero coordinate domains form a lattice-invariant
open cover for the infinitesimal theta gauges. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

def thetaGaugeOpen (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) : Set Φ.space :=
  {z | F.coordinate i.1 z ≠ 0 ∧ G.coordinate i.2 z ≠ 0}

theorem thetaGaugeOpen_isOpen (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) :
    IsOpen (thetaGaugeOpen F G i) :=
  (isOpen_ne_fun (F.coordinate i.1).continuous continuous_const).inter
    (isOpen_ne_fun (G.coordinate i.2).continuous continuous_const)

theorem thetaGaugeOpen_cover (z : Φ.space) : ∃ i, z ∈ thetaGaugeOpen F G i := by
  obtain ⟨i, hi⟩ := thetaFamily_exists_nonzero_coordinate F z
  obtain ⟨j, hj⟩ := thetaFamily_exists_nonzero_coordinate G z
  exact ⟨(i, j), hi, hj⟩

theorem thetaGaugeOpen_translates (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (l : Φ.periodIntegerLattice) (z : Φ.space) : z + l.val ∈ thetaGaugeOpen F G i ↔ z ∈ thetaGaugeOpen F G i := by
  simp only [thetaGaugeOpen, Set.mem_ofPred_eq, (F.coordinate i.1).translates,
    (G.coordinate i.2).translates, mul_ne_zero_iff]
  exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h =>
    ⟨⟨pow_ne_zero _ (J.value_ne_zero l z), h.1⟩, ⟨pow_ne_zero _ (J.value_ne_zero l z), h.2⟩⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.GaugeOpens
