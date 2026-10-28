import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy

/-! # Closed Ball -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles

noncomputable section

/-!
# Relative fundamental classes of closed coordinate balls

The relative groups are the homology of the actual singular-chain quotient
for `(E, E \ closedBall 0 r)`. The inclusion into the punctured pair is a
quasi-isomorphism because the outside-ball inclusion is a genuine homotopy
equivalence. Its inverse transports the existing coordinate-normalized local
class. An explicit translation homotopy proves the normalization at every
point of the closed ball. No invariance under nonlinear coordinate changes
is assumed here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (E : Type) [NormedAddCommGroup E]

/-- The identity map sends the outside of a closed ball into the complement
of each point of that ball. -/
theorem closedBallOutside_mapsTo_point (r : ℝ) (x : E)
    (hx : x ∈ Metric.closedBall (0 : E) r) :
    Set.MapsTo (𝟙 (TopCat.of E)) (ClosedBallRadial.Cycles.OutsideClosedBall E r) ({x}ᶜ : Set E) := by
  intro y hy
  change y ≠ x
  rintro rfl
  exact hy hx

/-- The genuine relative-chain restriction from a closed ball to one of its points. -/
def closedBallPointChainMap (r : ℝ) (x : E)
    (hx : x ∈ Metric.closedBall (0 : E) r) :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of E) (ClosedBallRadial.Cycles.OutsideClosedBall E r) ⟶
      LocalHomology.Cycles.relativeSingularChains (TopCat.of E) ({x}ᶜ : Set E) :=
  LocalHomology.Cycles.relativeSingularChainsMap (𝟙 (TopCat.of E)) (closedBallOutside_mapsTo_point E r x hx)

/-- The induced restriction from closed-ball relative homology to point-local homology. -/
abbrev closedBallPointHomologyMap (r : ℝ) (x : E)
    (hx : x ∈ Metric.closedBall (0 : E) r) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of E) (ClosedBallRadial.Cycles.OutsideClosedBall E r) n ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) x n :=
  HomologicalComplex.homologyMap (closedBallPointChainMap E r x hx) n

variable [NormedSpace ℝ E]

/-- The restriction to the center is a quasi-isomorphism in every degree.
This follows from the two actual short exact relative-chain sequences. -/
theorem closedBallOriginChainMap_quasiIso (r : ℝ) (hr : 0 ≤ r) :
    QuasiIso (closedBallPointChainMap E r 0 (Metric.mem_closedBall_self hr)) := by
  let φ := RelativeHomologyExact.Cycles.relativeChainSequenceMap (𝟙 (TopCat.of E))
    (closedBallOutside_mapsTo_point E r 0 (Metric.mem_closedBall_self hr))
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (LocalHomology.Cycles.relativeChainSequence_shortExact (TopCat.of E) (ClosedBallRadial.Cycles.OutsideClosedBall E r))
    (LocalHomology.Cycles.relativeChainSequence_shortExact (TopCat.of E) ({0}ᶜ : Set E))
  · exact (ContractibleModel.Cycles.singularChainsHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of (ClosedBallRadial.Cycles.OutsideClosedBall E r)) (Y := TopCat.of (NormalSphere.Cycles.PuncturedNormal E))
      (ClosedBallRadial.Cycles.outsideClosedBallHomotopyEquiv E r hr)).quasiIso_hom
  · change QuasiIso (LocalHomology.Cycles.integralSingularChainFunctor.map (𝟙 (TopCat.of E)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- Closed-ball relative homology agrees with local homology at the center,
through the map induced by inclusion of the two actual subspaces. -/
def closedBallOriginHomologyIso (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of E) (ClosedBallRadial.Cycles.OutsideClosedBall E r) n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n := by
  have := closedBallOriginChainMap_quasiIso E r hr
  exact isoOfQuasiIsoAt (closedBallPointChainMap E r 0 (Metric.mem_closedBall_self hr)) n

@[simp]
theorem closedBallOriginHomologyIso_hom (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (closedBallOriginHomologyIso E r hr n).hom =
      closedBallPointHomologyMap E r 0 (Metric.mem_closedBall_self hr) n := rfl

/-- Translation to the origin identifies the actual point-local homology groups. -/
def localTranslationHomologyIso (x : E) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of E) x n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n :=
  LocalHomology.Cycles.relativeSingularHomologyIso (Homeomorph.subRight x)
    (by
      intro y
      change y ≠ x ↔ y - x ≠ (0 : E)
      exact ⟨fun h hzero => h (sub_eq_zero.mp hzero),
        fun h heq => h (sub_eq_zero.mpr heq)⟩) n

/-- The straight translation homotopy from the identity to subtraction of `x`. -/
def coordinateTranslationHomotopy (x : E) :
    TopCat.Homotopy (𝟙 (TopCat.of E)) (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E) (Homeomorph.subRight x)).hom where
  toFun z := z.2 - (z.1 : ℝ) • x
  continuous_toFun := by fun_prop
  map_zero_left y := by simp
  map_one_left y := by simp

/-- Translating by a fraction of a point in the ball cannot move an outside
point to the origin. This includes points on the boundary of the closed ball. -/
theorem coordinateTranslationHomotopy_mapsTo (r : ℝ) (x : E)
    (hx : x ∈ Metric.closedBall (0 : E) r) (t : unitInterval) :
    Set.MapsTo (fun y => coordinateTranslationHomotopy E x (t, y))
      (ClosedBallRadial.Cycles.OutsideClosedBall E r) ({0}ᶜ : Set E) := by
  intro y hy
  change y - (t : ℝ) • x ≠ (0 : E)
  intro hz
  have he : y = (t : ℝ) • x := sub_eq_zero.mp hz
  have hbound : ‖(t : ℝ) • x‖ ≤ r := by
    rw [norm_smul, Real.norm_of_nonneg t.property.1]
    exact (mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg x)).trans
      (by simpa only [one_mul] using mem_closedBall_zero_iff.mp hx)
  have hout := ClosedBallRadial.Cycles.outsideClosedBall_norm E r ⟨y, hy⟩
  change r < ‖y‖ at hout
  rw [he] at hout
  exact (not_lt_of_ge hbound) hout

/-- Restriction to any point of the ball, followed by translation to the
origin, equals restriction to the center. -/
@[reassoc]
theorem closedBallPointHomologyMap_translation (r : ℝ) (hr : 0 ≤ r)
    (x : E) (hx : x ∈ Metric.closedBall (0 : E) r) (n : ℕ) :
    closedBallPointHomologyMap E r x hx n ≫ (localTranslationHomologyIso E x n).hom =
      closedBallPointHomologyMap E r 0 (Metric.mem_closedBall_self hr) n := by
  let htrans : Set.MapsTo (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E) (Homeomorph.subRight x)).hom
      ({x}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro y hy
    change (y : E) - x ≠ (0 : E)
    exact sub_ne_zero.mpr hy
  change LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 (TopCat.of E))
      (closedBallOutside_mapsTo_point E r x hx) n ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E) (Homeomorph.subRight x)).hom htrans n = _
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp]
  exact (RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy
    (closedBallOutside_mapsTo_point E r 0 (Metric.mem_closedBall_self hr))
    (fun _ hy => htrans (closedBallOutside_mapsTo_point E r x hx hy))
    (coordinateTranslationHomotopy E x)
    (coordinateTranslationHomotopy_mapsTo E r x hx) n).symm

/-- Relative top homology of a complex coordinate closed ball is `ℤ`, using
the already specified point-local coordinate normalization. -/
def complexClosedBallTopHomologyIso (p : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ)) (ClosedBallRadial.Cycles.OutsideClosedBall (Fin p → ℂ) r)
      (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  closedBallOriginHomologyIso (Fin p → ℂ) r hr (2 * p) ≪≫ ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The actual closed-ball relative class normalized to one in the chosen
complex coordinate local-homology isomorphism. -/
def complexClosedBallClass (p : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ)) (ClosedBallRadial.Cycles.OutsideClosedBall (Fin p → ℂ) r)
      (2 * p) :=
  (complexClosedBallTopHomologyIso p r hr).inv 1

/-- Restricting the closed-ball class to its center gives precisely the
existing normalized local generator. -/
theorem complexClosedBallClass_origin (p : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    closedBallPointHomologyMap (Fin p → ℂ) r 0 (Metric.mem_closedBall_self hr) (2 * p)
        (complexClosedBallClass p r hr) =
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1 := by
  exact ConcreteCategory.congr_hom
    (closedBallOriginHomologyIso (Fin p → ℂ) r hr (2 * p)).inv_hom_id
    ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- Point-local coordinate normalization obtained by the actual translation
to the origin. -/
def complexCoordinatePointHomologyIso (p : ℕ) (x : Fin p → ℂ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) x (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  localTranslationHomologyIso (Fin p → ℂ) x (2 * p) ≪≫ ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The normalized coordinate local class at an arbitrary point. -/
def complexCoordinatePointClass (p : ℕ) (x : Fin p → ℂ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) x (2 * p) :=
  (complexCoordinatePointHomologyIso p x).inv 1

/-- The translated coordinate local class maps back to the specified origin class. -/
theorem complexCoordinatePointClass_to_origin (p : ℕ) (x : Fin p → ℂ) :
    (localTranslationHomologyIso (Fin p → ℂ) x (2 * p)).hom
        (complexCoordinatePointClass p x) =
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1 :=
  ConcreteCategory.congr_hom
    (localTranslationHomologyIso (Fin p → ℂ) x (2 * p)).inv_hom_id
    ((ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1)

/-- The closed-ball class restricts to the normalized coordinate local class
at every point of the closed ball, in particular at every interior point. -/
theorem complexClosedBallClass_atPoint (p : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (x : Fin p → ℂ) (hx : x ∈ Metric.closedBall 0 r) :
    closedBallPointHomologyMap (Fin p → ℂ) r x hx (2 * p)
        (complexClosedBallClass p r hr) = complexCoordinatePointClass p x := by
  apply (ConcreteCategory.bijective_of_isIso
    (localTranslationHomologyIso (Fin p → ℂ) x (2 * p)).hom).1
  calc
    _ = closedBallPointHomologyMap (Fin p → ℂ) r 0 (Metric.mem_closedBall_self hr) (2 * p)
        (complexClosedBallClass p r hr) :=
      ConcreteCategory.congr_hom
        (closedBallPointHomologyMap_translation (Fin p → ℂ) r hr x hx (2 * p)) _
    _ = (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1 := complexClosedBallClass_origin p r hr
    _ = _ := (complexCoordinatePointClass_to_origin p x).symm

/-- All other relative degrees vanish for a complex closed coordinate ball. -/
theorem complexClosedBallHomology_isZero (p n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hn : n ≠ 2 * p) :
    IsZero (LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin p → ℂ))
      (ClosedBallRadial.Cycles.OutsideClosedBall (Fin p → ℂ) r) n) :=
  (ComplexLocalVanishing.Cycles.complexNormalLocalHomology_isZero p n hn).of_iso
    (closedBallOriginHomologyIso (Fin p → ℂ) r hr n)

/-- The coordinate ball supporting the relative class is actually compact. -/
theorem complexClosedBall_isCompact (p : ℕ) (r : ℝ) :
    IsCompact (Metric.closedBall (0 : Fin p → ℂ) r) :=
  isCompact_closedBall 0 r

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles
