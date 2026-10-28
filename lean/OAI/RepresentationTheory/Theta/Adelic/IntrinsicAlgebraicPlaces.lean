import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
import OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace
import OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Intrinsic Algebraic Places -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicAlgebraicPlaces.Intrinsic

noncomputable section

/-! The native archimedean product is the actual full diagonal
realization of the constructed algebraic group. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.Topology OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace
open OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def nativeAtPlaceContinuousEquiv (v : NumberField.InfinitePlace F) :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v)) ≃ₜ* (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).AtPlace v :=
  UnitaryAlgebraicModel.Topology.regularUnitaryContinuousEquiv (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v) d) (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v))

def nativeArchimedeanContinuousEquiv : RationalSU.ArchimedeanSU F H ≃ₜ*
    (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).ArchimedeanProduct Set.univ where
  toFun g v := nativeAtPlaceContinuousEquiv F d H v.val (g v.val)
  invFun g v := (nativeAtPlaceContinuousEquiv F d H v).symm (g ⟨v, Set.mem_univ v⟩)
  left_inv g := by
    funext v
    exact (nativeAtPlaceContinuousEquiv F d H v).symm_apply_apply _
  right_inv g := by
    funext v
    exact (nativeAtPlaceContinuousEquiv F d H v.val).apply_symm_apply _
  map_mul' g h := by
    funext v
    exact map_mul (nativeAtPlaceContinuousEquiv F d H v.val) _ _
  continuous_toFun := continuous_pi fun v =>
    (nativeAtPlaceContinuousEquiv F d H v.val).continuous.comp (continuous_apply v.val)
  continuous_invFun := continuous_pi fun v =>
    (nativeAtPlaceContinuousEquiv F d H v).symm.continuous.comp
      (continuous_apply (⟨v, Set.mem_univ v⟩ : (Set.univ : Set (NumberField.InfinitePlace F))))

theorem nativeArchimedean_diagonal (g : SpecialUnitary.SU H.val) :
    nativeArchimedeanContinuousEquiv F d H (RationalSU.rationalArchimedeanSU F H g) =
      (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).diagonal Set.univ (UnitaryAlgebraicModel.regularUnitaryEquiv d H.val g) := by
  funext v
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v.val) d)
      (g.val.val.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v.val)))) i j =
    Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v.val) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val i j)
  exact congrArg (fun M : Matrix (Fin 6) (Fin 6) v.val.Completion => M i j)
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_map d (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v.val)) g.val.val)

variable {F d H} {m : ℕ} {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

include A in
theorem unitary_compact_real_place (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    ∃ v : F →+* ℝ, NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsCompactAtRealPlace
      (UnitaryConnected.connectedSemisimpleUnitaryGroup d H hd hH) v := by
  obtain ⟨v, hv⟩ := A.other_place
  let G := UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val
  let e := nativeAtPlaceContinuousEquiv F d H (A.enumerate v)
  let : CompactSpace (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) := CompactDefinitePlace.native_definite_compact A v hv
  let : CompactSpace (G.AtPlace (A.enumerate v)) := e.toHomeomorph.compactSpace
  let f := (A.real v).toRingHom.comp (algebraMap F (A.enumerate v).Completion)
  refine ⟨f, ?_⟩
  exact (G.pointsContinuousMulEquiv (algebraMap F (A.enumerate v).Completion)
    (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)).toHomeomorph.compactSpace

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicAlgebraicPlaces.Intrinsic
