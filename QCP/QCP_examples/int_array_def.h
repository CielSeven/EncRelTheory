/*@ Extern Coq (sum : list Z -> Z) 
               (sublist : {A} -> Z -> Z -> list A -> list A)
               (store_int_array : Z -> Z -> list Z -> Assertion)
               (store_int_array_missing_i_rec: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (store_array_box: Z -> Z -> list Z -> Assertion)
               (store_array_box_array: Z -> list Z -> Assertion)
               (store_int_array_rec: Z -> Z -> Z -> list Z -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (replace_Znth: {A} -> Z -> A -> list A -> list A)
               (zeros: Z -> list Z)
*/

/*@ include strategies "int_array.strategies" */