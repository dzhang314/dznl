#ifndef DZNL_FIXED_SIZE_ARRAY_HPP_INCLUDED
#define DZNL_FIXED_SIZE_ARRAY_HPP_INCLUDED

namespace dznl {


template <typename ITEM_T, typename INDEX_T, INDEX_T SIZE>
struct FixedSizeArray {

    ITEM_T items[SIZE];

    constexpr ITEM_T &operator[](INDEX_T index) noexcept {
        return items[index];
    }

    constexpr const ITEM_T &operator[](INDEX_T index) const noexcept {
        return items[index];
    }

}; // struct FixedSizeArray<ITEM_T, INDEX_T, SIZE>


} // namespace dznl

#endif // DZNL_FIXED_SIZE_ARRAY_HPP_INCLUDED
