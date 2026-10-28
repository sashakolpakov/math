import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialCurves

/-! # Finite Adelic Comparison -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison

noncomputable section

/-! Removing exactly the archimedean places identifies the Arithmetic away
adeles with the restricted product over all finite places. -/

open scoped Classical _root_.NumberField RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def allArchimedeanPlaces : Finset (LocalAdeles.Place F) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

theorem mem_allArchimedeanPlaces (v : NumberField.InfinitePlace F) :
    Sum.inl v ∈ allArchimedeanPlaces (F := F) := by simp [allArchimedeanPlaces]

def finiteAwayIndex (v : HeightOneSpectrum (𝓞 F)) : ApproximationTopology.AwayPlace (allArchimedeanPlaces (F := F)) :=
  ⟨Sum.inr v, by simp [allArchimedeanPlaces]⟩

theorem finiteAwayIndex_injective : Function.Injective (finiteAwayIndex (F := F)) := by
  intro v w h
  exact Sum.inr_injective (congrArg Subtype.val h)

def diagonalFiniteAdelic (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) : G.RationalPoints →* FiniteAdelicMatrices.FiniteAdelicGroupPoints G where
  toFun g := ⟨fun v => LocalAdeles.diagonalLocal G (.inr v) g,
    (show Function.Injective (Sum.inr : HeightOneSpectrum (𝓞 F) → LocalAdeles.Place F) from
      Sum.inr_injective).tendsto_cofinite (LocalAdeles.eventually_integral_diagonal G g)⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (LocalAdeles.diagonalLocal G (.inr v))
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (LocalAdeles.diagonalLocal G (.inr v)) g h

def awayToFiniteAdelicHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    LocalAdeles.AwayAdelicPoints G allArchimedeanPlaces →* FiniteAdelicMatrices.FiniteAdelicGroupPoints G :=
  RestrictedProduct.mapAlongMonoidHom
    (fun w : ApproximationTopology.AwayPlace (allArchimedeanPlaces (F := F)) => LocalAdeles.LocalPoints G w.val)
    (fun v : HeightOneSpectrum (𝓞 F) => LocalAdeles.LocalPoints G (.inr v))
    finiteAwayIndex finiteAwayIndex_injective.tendsto_cofinite
    (fun _ => MonoidHom.id _) (Filter.Eventually.of_forall (fun _ _ hx => hx))

def finiteToAwayAdelicHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    FiniteAdelicMatrices.FiniteAdelicGroupPoints G →* LocalAdeles.AwayAdelicPoints G allArchimedeanPlaces :=
  RestrictedProduct.mapAlongMonoidHom
    (fun v : HeightOneSpectrum (𝓞 F) => LocalAdeles.LocalPoints G (.inr v))
    (fun w : ApproximationTopology.AwayPlace (allArchimedeanPlaces (F := F)) => LocalAdeles.LocalPoints G w.val)
    (SelectedArithmeticProduct.awayFinitePlace allArchimedeanPlaces mem_allArchimedeanPlaces)
    (AdelicPolynomialCurves.awayFinitePlace_injective allArchimedeanPlaces mem_allArchimedeanPlaces).tendsto_cofinite
    (fun w => (SelectedArithmeticProduct.localPointsPlaceEquiv G (SelectedArithmeticProduct.inr_awayFinitePlace allArchimedeanPlaces mem_allArchimedeanPlaces w)).toMonoidHom)
    (Filter.Eventually.of_forall (fun w _ hx =>
      (AdelicPolynomialCurves.localPointsPlaceEquiv_mem_integral G
        (SelectedArithmeticProduct.inr_awayFinitePlace allArchimedeanPlaces mem_allArchimedeanPlaces w) _).mpr hx))

theorem awayToFiniteAdelicHom_surjective (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    Function.Surjective (awayToFiniteAdelicHom G) := by
  intro g
  refine ⟨finiteToAwayAdelicHom G g, ?_⟩
  apply RestrictedProduct.ext
  intro v
  rfl

theorem awayToFiniteAdelicHom_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    Continuous (awayToFiniteAdelicHom G) :=
  RestrictedProduct.mapAlong_continuous
    (fun w : ApproximationTopology.AwayPlace (allArchimedeanPlaces (F := F)) => LocalAdeles.LocalPoints G w.val)
    (fun v : HeightOneSpectrum (𝓞 F) => LocalAdeles.LocalPoints G (.inr v))
    (A₁ := fun w => (LocalAdeles.integralLocalSubgroup G w.val : Set (LocalAdeles.LocalPoints G w.val)))
    (A₂ := fun v => (LocalAdeles.integralLocalSubgroup G (.inr v) : Set (LocalAdeles.LocalPoints G (.inr v))))
    finiteAwayIndex finiteAwayIndex_injective.tendsto_cofinite (fun _ g => g)
    (Filter.Eventually.of_forall (fun _ _ hx => hx)) (fun _ => continuous_id)

theorem awayToFiniteAdelicHom_diagonal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.RationalPoints) :
    awayToFiniteAdelicHom G (LocalAdeles.diagonalAway G allArchimedeanPlaces g) = diagonalFiniteAdelic G g := rfl

theorem denseRange_diagonalFiniteAdelic_of_away (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (h : DenseRange (LocalAdeles.diagonalAway G allArchimedeanPlaces)) : DenseRange (diagonalFiniteAdelic G) := by
  have hd := (awayToFiniteAdelicHom_surjective G).denseRange.comp h (awayToFiniteAdelicHom_continuous G)
  exact hd

theorem finiteAdelicMatrix_diagonal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.RationalPoints) :
    FiniteAdelicMatrices.finiteAdelicMatrix G (diagonalFiniteAdelic G g) = g.val.val.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) := rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison
