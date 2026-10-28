import Mathlib.RingTheory.IsTensorProduct

/-! # Scalar Extension Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ScalarExtensionMap

noncomputable section

/-! A map from the original affine family extends uniquely to its
actual scalar extension, preserving the new base algebra and its values
on the original regular functions. -/

variable (R D S P T : Type) [CommRing R] [CommRing D] [CommRing S] [CommRing P] [CommRing T]
    [Algebra R D] [Algebra R S] [Algebra R P] [Algebra R T]
    [Algebra D P] [Algebra D T] [Algebra S P]
    [IsScalarTower R D P] [IsScalarTower R S P] [IsScalarTower R D T]
    [Algebra.IsPushout R D S P]

def affineScalarExtensionMap (f : S →ₐ[R] T) : P →ₐ[D] T where
  __ := (Algebra.pushoutDesc P (IsScalarTower.toAlgHom R D T) f (fun _ _ => mul_comm _ _)).toRingHom
  commutes' d := Algebra.pushoutDesc_left P (IsScalarTower.toAlgHom R D T) f (fun _ _ => mul_comm _ _) d

theorem affineScalarExtensionMap_algebraMap (f : S →ₐ[R] T) (s : S) :
    affineScalarExtensionMap R D S P T f (algebraMap S P s) = f s :=
  Algebra.pushoutDesc_right P (IsScalarTower.toAlgHom R D T) f (fun _ _ => mul_comm _ _) s

theorem affineScalarExtensionMap_unique (f : S →ₐ[R] T) (g : P →ₐ[D] T)
    (h : ∀ s : S, g (algebraMap S P s) = f s) :
    g = affineScalarExtensionMap R D S P T f := by
  have H : g.restrictScalars R = (affineScalarExtensionMap R D S P T f).restrictScalars R := by
    apply Algebra.IsPushout.algHom_ext (R := R) (S := D) (R' := S)
    · apply AlgHom.ext
      intro s
      exact (h s).trans (affineScalarExtensionMap_algebraMap R D S P T f s).symm
    · apply AlgHom.ext
      intro d
      exact (g.commutes d).trans ((affineScalarExtensionMap R D S P T f).commutes d).symm
  apply AlgHom.ext
  intro p
  exact AlgHom.congr_fun H p

theorem affineScalarExtensionMap_reduction
    (B : Type) [CommRing B] [Algebra R B] [Algebra D B] [IsScalarTower R D B]
    (f : S →ₐ[R] T) (qP : P →ₐ[D] B) (qT : T →ₐ[D] B)
    (h : ∀ s : S, qT (f s) = qP (algebraMap S P s)) :
    qT.comp (affineScalarExtensionMap R D S P T f) = qP := by
  let u := (qT.restrictScalars R).comp f
  have hP : qP = affineScalarExtensionMap R D S P B u :=
    affineScalarExtensionMap_unique R D S P B u qP (fun s => (h s).symm)
  have hT : qT.comp (affineScalarExtensionMap R D S P T f) =
      affineScalarExtensionMap R D S P B u := by
    apply affineScalarExtensionMap_unique R D S P B u
    intro s
    change qT (affineScalarExtensionMap R D S P T f (algebraMap S P s)) = qT (f s)
    rw [affineScalarExtensionMap_algebraMap]
  exact hT.trans hP.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ScalarExtensionMap
