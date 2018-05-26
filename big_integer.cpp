//
// Created by rsbat on 5/23/18.
//

#include "big_integer.h"

#include <limits>
#include <cassert>
#include <functional>
#include <algorithm>

typedef uint32_t ui;
typedef uint64_t ull;
typedef std::vector<ui> storage_t;

const int BITS = 32;
const ui UI_MAX = std::numeric_limits<ui>::max();

template <typename T>
ui uicast(const T& x) {
    return static_cast<ui>(x);
}

template <typename T>
ull ullcast(const T& x) {
    return static_cast<ull>(x);
}

big_integer::big_integer() :isNegative(false), isSmall(true), smallnumber(0) {

}

big_integer::big_integer(const big_integer &other) :isNegative(other.isNegative), isSmall(other.isSmall) {
    if (isSmall) {
        smallnumber = other.smallnumber;
    } else {
        new(&number) std::shared_ptr<storage_t>();
        number = other.number;
    }
}

big_integer::big_integer(int a) :isNegative(a < 0), isSmall(true), smallnumber(a < 0 ? ~uicast(a) + 1 : uicast(a)) {

}

big_integer::big_integer(std::string const &str) :big_integer() {
    big_integer res;

    for (auto ch : str) {
        if (ch == '-') { continue; }
        res = res * 10 + (ch - '0');
    }

    if (str[0] == '-') { res = -res; }
    std::swap(*this, res);
}

big_integer::~big_integer() {
    if (!isSmall) {
        number.~shared_ptr();
    }
}

big_integer &big_integer::operator=(big_integer const &other) {
    isNegative = other.isNegative;

    if (isSmall != other.isSmall) {
        if (isSmall) {
            to_big();
            number = other.number;
        } else {
            to_small();
            smallnumber = other.smallnumber;
        }
    } else {
        if (isSmall) {
            smallnumber = other.smallnumber;
        } else {
            number = other.number;
        }
    }
    isSmall = other.isSmall;
    return *this;
}

// function will add space to store result
// strong guarantee
void add_vec_vec(storage_t& lhs, const storage_t& rhs) {
    size_t m = std::max(lhs.size(), rhs.size()) + 1;
    lhs.resize(m, 0);

    ull carry = 0;
    for (size_t i = 0; i < rhs.size(); i++) {
        ull tmp = carry + lhs[i] + rhs[i];
        lhs[i] = uicast(tmp);
        carry = tmp >> BITS;
    }

    std::for_each(lhs.begin() + rhs.size(), lhs.end(), [&carry](ui& x) {
        carry += x;
        x = uicast(carry);
        carry >>= BITS;
    });
}

void add_vec_num(storage_t& lhs, const ui rhs) {
    lhs.push_back(0);

    ull carry = rhs;
    std::for_each(lhs.begin(), lhs.end(), [&carry](ui& x) {
        carry += x;
        x = uicast(carry);
        carry >>= BITS;
    });
}

big_integer &big_integer::operator+=(big_integer const &rhs) {
    if (isNegative != rhs.isNegative) {
        isNegative = !isNegative;
        *this -= rhs;
        if (!size() == 0) { isNegative = !isNegative; }
        return *this;
    }

    if (isSmall && rhs.isSmall) {
        ull res = toulong() + rhs.toulong();
        if (uicast(res >> BITS) == 0) {
            smallnumber = uicast(res);
        } else {
            to_big(res);
        }
    } else {
        to_big();
        make_unique_storage();
        if (rhs.isSmall) {
            add_vec_num(*number, rhs.smallnumber);
        } else {
            add_vec_vec(*number, *rhs.number);
        }
        remove_leading_zeros();
    }
    return *this;
}

void sub_vec_vec(storage_t& lhs, const storage_t& rhs) {
    size_t m = std::max(lhs.size(), rhs.size()) + 1;
    lhs.resize(m, 0);

    ull carry = 1;
    for (size_t i = 0; i < rhs.size(); i++) {
        ull tmp = carry + lhs[i] + ~rhs[i];
        lhs[i] = uicast(tmp);
        carry = tmp >> BITS;
    }

    std::for_each(lhs.begin() + rhs.size(), lhs.end(), [&carry](ui& x) {
        carry += ullcast(UI_MAX) + x;
        x = uicast(carry);
        carry >>= BITS;
    });
}

void sub_vec_num(storage_t& lhs, const ui rhs) {
    lhs.push_back(0);

    ull carry = 1ull + ~rhs;

    std::for_each(lhs.begin(), lhs.end(), [&carry](ui& x) {
        carry += ullcast(UI_MAX) + x;
        x = uicast(carry);
        carry >>= BITS;
    });
}

big_integer &big_integer::operator-=(big_integer const &rhs) {
    if (isNegative != rhs.isNegative) {
        isNegative = !isNegative;
        *this += rhs;
        if (!size() == 0) { isNegative = !isNegative; }
        return *this;
    }

    if ((*this < rhs) ^ isNegative) {
        *this = rhs - *this;
        if (!size() == 0) { isNegative = !isNegative; }
        return *this;
    }

    if (isSmall && rhs.isSmall) {
        ull res = toulong() + ~rhs.toulong() + 1;
        if (uicast(res >> BITS) == 0) {
            smallnumber = uicast(res);
            if (smallnumber == 0) { isNegative = false; }
        } else {
            to_big(res);
        }
    } else {
        to_big();
        make_unique_storage();
        if (rhs.isSmall) {
            sub_vec_num(*number, rhs.smallnumber);
        } else {
            sub_vec_vec(*number, *rhs.number);
        }
        remove_leading_zeros();
    }
    return *this;
}

// multiplies two positive vectors
// strong guarantee
void mul_vec_vec(storage_t& lhs, const storage_t& rhs) {
    size_t n = lhs.size();
    size_t m = rhs.size();

    std::vector<ui> result(n + m, 0);

    for (size_t i = 0; i < m; i++) {
        ull carry = 0;
        for (size_t j = 0; j < n || carry; j++) {
            ull tmp = carry + result[i + j] + ullcast(j < n ? lhs[j] : 0) * rhs[i];
            result[i + j] = uicast(tmp);
            carry = tmp >> BITS;
        }
    }

    lhs.swap(result);
}

// multiplies vector of any sign by a number
void mul_vec_num(storage_t& lhs, const ui rhs) {
    lhs.push_back(0);

    ull carry = 0;
    for (auto& x : lhs) {
        carry += ullcast(x) * rhs;
        x = uicast(carry);
        carry >>= BITS;
    }
}

big_integer &big_integer::operator*=(big_integer const &rhs) {
    if (isSmall && rhs.isSmall) {
        ull res = ullcast(smallnumber) * rhs.smallnumber;
        if (uicast(res >> BITS) == 0) {
            smallnumber = uicast(res);
        } else {
            to_big(res);
        }
    } else {
        to_big();
        make_unique_storage();
        if (rhs.isSmall) {
            mul_vec_num(*number, rhs.smallnumber);
        } else {
            mul_vec_vec(*number, *rhs.number);
        }
        remove_leading_zeros();
    }
    isNegative ^= rhs.isNegative;
    if (size() == 0) { isNegative = false; }
    return *this;
}

// lhs and rhs must be positive, lhs.size must be at least rhs.size + sh
// lhs = lhs - (rhs * BASE ^ sh)
void sub_with_shift(storage_t &lhs, const storage_t &rhs, long sh) {
    ull carry = 1;
    size_t m = rhs.size() + sh;
    lhs.push_back(0);

    for (size_t i = sh; i < m; i++) {
        carry += ullcast(lhs[i]) + ~rhs[i - sh];
        lhs[i] = uicast(carry);
        carry >>= BITS;
    }

    if (carry == 0) {
        std::for_each(lhs.begin() + m, lhs.end(), [&carry](ui& x) {
            carry += ullcast(UI_MAX) + x;
            x = uicast(carry);
            carry >>= BITS;
        });
    }
}

// lhs and rhs must be positive, lhs >= rhs
void add_with_shift(storage_t &lhs, const storage_t& rhs, long sh) {
    ull carry = 0;
    size_t m = rhs.size() + sh;
    lhs.push_back(0);

    for (size_t i = sh; i < m; i++) {
        carry += ullcast(lhs[i]) + rhs[i - sh];
        lhs[i] = uicast(carry);
        carry >>= BITS;
    }

    std::for_each(lhs.begin() + m, lhs.end(), [&carry](ui& x) {
        carry += x;
        x = uicast(carry);
        carry >>= BITS;
    });
}

// true if lhs < rhs * (BASE ^ sh)  as number (not lexicographically)
bool vec_less(const storage_t& lhs, const storage_t& rhs, size_t sh = 0) {
    if (lhs.size() != rhs.size() + sh) { return lhs.size() < rhs.size() + sh; }
    if (lhs.empty()) { return false; }

    for (size_t i = lhs.size() - 1; i > sh; i--) {
        if (lhs[i] != rhs[i - sh]) { return lhs[i] < rhs[i - sh]; }
    }

    return lhs[sh] < rhs[0];
}

//divides two positive vectors
//TODO optimize
void div_vec_vec(storage_t& lhs, const storage_t& rhs) {
    size_t m = lhs.size() - rhs.size();
    size_t n = rhs.size();
    std::vector<ui> res(m + 1, 0);

    if (!vec_less(lhs, rhs, m)) {
        sub_with_shift(lhs, rhs, m);
        while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
        res[m] = 1;
    }

    for (long i = m - 1; i >= 0; i--) {
        ull q;

        if (lhs.empty()) {
            q = 0;
        } else {
            q = ((ullcast(lhs[n + i]) << BITS) + lhs[n + i - 1]) / rhs.back();
            q = std::min(q, ullcast(UI_MAX));
        }

        if (q != 0) {
            storage_t tmp(rhs);
            mul_vec_num(tmp, uicast(q));
            while (!tmp.empty() && tmp.back() == 0) { tmp.pop_back(); }

            while (vec_less(lhs, tmp, i)) {
                q--;
                add_with_shift(lhs, rhs, i);
                while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
            }
            sub_with_shift(lhs, tmp, i);
            while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
        }

        res[i] = uicast(q);
    }

    lhs.swap(res);
}
/*
void div_vec_num(storage_t& lhs, const ui rhs) {
    size_t m = lhs.size() - 1;
    size_t n = 1;
    std::vector<ui> res(m + 1, 0);

    if (!vec_less(lhs, rhs, m)) {
        sub_with_shift(lhs, rhs, m);
        while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
        res[m] = 1;
    }

    for (long i = m - 1; i >= 0; i--) {
        ull q;

        if (lhs.empty()) {
            q = 0;
        } else {
            q = ((ullcast(lhs[n + i]) << BITS) + lhs[n + i - 1]) / rhs;
            q = std::min(q, ullcast(UI_MAX));
        }

        if (q != 0) {
            storage_t tmp(rhs);
            mul_vec_num(tmp, uicast(q));
            while (!tmp.empty() && tmp.back() == 0) { tmp.pop_back(); }

            while (vec_less(lhs, tmp, i)) {
                q--;
                add_with_shift(lhs, rhs, i);
                while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
            }
            sub_with_shift(lhs, tmp, i);
            while (!lhs.empty() && lhs.back() == 0) { lhs.pop_back(); }
        }

        res[i] = uicast(q);
    }

    lhs.swap(res);
}
*/

big_integer &big_integer::operator/=(big_integer const &rhs) {
    if (size() < rhs.size()) {
        to_small();
        isNegative = false;
        return *this;
    }

    if (isSmall && rhs.isSmall) {
        ull res = ullcast(smallnumber) / rhs.smallnumber;
        if (uicast(res >> BITS) == 0) {
            smallnumber = uicast(res);
        } else {
            to_big(res);
        }
    } else {
        to_big();
        make_unique_storage();
        if (rhs.isSmall) {
            ui tmp = rhs.smallnumber;
            int sh = 0;
            while (tmp < (1u << 31)) { tmp <<= 1; sh++; }
            *this <<= sh;
            div_vec_vec(*number, {tmp});
        } else {
            ui tmp = rhs.number->back();
            int sh = 0;
            while (tmp < (1u << 31)) { tmp <<= 1; sh++; }

            big_integer crhs(rhs);
            crhs <<= sh;
            *this <<= sh;
            div_vec_vec(*number, *crhs.number);
        }
        remove_leading_zeros();
    }
    isNegative ^= rhs.isNegative;
    if (size() == 0) { isNegative = false; }
    return *this;
}

big_integer &big_integer::operator%=(big_integer const &rhs) {
    auto ans = *this - (*this / rhs) * rhs;
    std::swap(*this, ans);
    return *this;
}

big_integer &big_integer::operator*=(int32_t rhs) {
    *this *= uicast(std::abs(rhs));

    if (rhs < 0) {
        isNegative = !isNegative;
    }
    return *this;
}

big_integer &big_integer::operator*=(uint32_t rhs) {
    if (isSmall) {
        ull res = ullcast(smallnumber) * rhs;
        if ((res >> BITS) == 0) {
            smallnumber = uicast(res);
        } else {
            to_big(res);
        }
    } else {
        make_unique_storage();
        mul_vec_num(*number, rhs);
        remove_leading_zeros();
    }
    return *this;
}

ui getPadding(bool sign) {
    return sign ? UI_MAX : 0;
}

void make_bin_op(storage_t& lhs, const storage_t& rhs, ui lpadding, ui rpadding, const std::function<ui(ui, ui)>& f) {
    size_t n = std::max(lhs.size(), rhs.size());
    lhs.resize(n, lpadding);
    
    for (size_t i = 0; i < n; i++) {
        lhs[i] = f(lhs[i], (i < rhs.size() ? rhs[i] : rpadding));
    }
}

big_integer &big_integer::operator&=(big_integer const &rhs) {
    storage_t res = to_complement();
    make_bin_op(res, rhs.to_complement(), getPadding(isNegative), getPadding(rhs.isNegative), std::bit_and<>());
    from_complement(res);
    return *this;
}


big_integer &big_integer::operator|=(big_integer const &rhs) {
    storage_t res = to_complement();
    make_bin_op(res, rhs.to_complement(), getPadding(isNegative), getPadding(rhs.isNegative), std::bit_or<>());
    from_complement(res);
    return *this;
}


big_integer &big_integer::operator^=(big_integer const &rhs) {
    storage_t res = to_complement();
    make_bin_op(res, rhs.to_complement(), getPadding(isNegative), getPadding(rhs.isNegative), std::bit_xor<>());
    from_complement(res);
    return *this;
}

void vec_shl(storage_t& vec, size_t sh) {
    if (sh == 0) { return; }
    storage_t res(vec.size() + sh, 0);
    std::copy(vec.begin(), vec.end(), vec.begin() + sh);
    vec = res;
}

big_integer &big_integer::operator<<=(int rhs) {
    to_big();
    make_unique_storage();

    int sh = rhs % BITS;
    if (sh != 0) {
        number->push_back(0);
        ui mask = UI_MAX << (BITS - sh);
        ui carry = 0;

        for (auto& x : *number) {
            ui tmp = (x & mask) >> (BITS - sh);
            x = (x << sh) | carry;
            carry = tmp;
        }
    }

    vec_shl(*number, uicast(rhs / BITS));
    remove_leading_zeros();
    return *this;
}

void vec_shr(storage_t& vec, size_t sh) {
    if (sh == 0) { return; }
    vec.assign(vec.begin() + sh, vec.end());
}

big_integer &big_integer::operator>>=(int rhs) {
    to_big();
    make_unique_storage();

    int sh = rhs % BITS;
    bool add1 = false;
    if (sh != 0) {
        number->push_back(0);
        ui mask = UI_MAX >> (BITS - sh);
        ui carry = 0;

        if ((*number)[0] & mask) { add1 = true; }
        for (auto& x : *number) {
            ui tmp = (x & mask) << (BITS - sh);
            x = (x >> sh) | carry;
            carry = tmp;
        }
    }

    vec_shr(*number, uicast(rhs / BITS));
    remove_leading_zeros();
    if (isNegative && add1) { *this += 1; }
    return *this;
}

big_integer big_integer::operator+() const {
    return *this;
}

big_integer big_integer::operator-() const {
    if (isSmall && smallnumber == 0) { return *this; }
    big_integer res(*this);
    res.isNegative = !res.isNegative;
    return res;
}

big_integer big_integer::operator~() const {
    return -(*this + 1);
}

big_integer &big_integer::operator++() {
    return *this += 1;
}

big_integer big_integer::operator++(int) {
    big_integer res(*this);
    *this += 1;
    return res;
}

big_integer &big_integer::operator--() {
    return *this -= 1;
}

big_integer big_integer::operator--(int) {
    big_integer res(*this);
    *this -= 1;
    return res;
}

bool operator==(big_integer const &a, big_integer const &b) {
    if (a.size() != b.size() || a.isNegative != b.isNegative) { return false; }

    if (a.isSmall) {
        return a.smallnumber == b.smallnumber;
    } else {
        for (auto lit = a.number->begin(), rit = b.number->begin(); lit != a.number->end(); lit++, rit++) {
            if (*lit != *rit) { return false; }
        }
    }

    return true;
}

bool operator!=(big_integer const &a, big_integer const &b) {
    return !(a == b);
}

bool operator<(big_integer const &a, big_integer const &b) {
    if (a.isNegative != b.isNegative) { return a.isNegative; }
    if (a.size() != b.size()) { return (a.size() < b.size()) ^ a.isNegative; }

    if (a.isSmall) {
        return (a.smallnumber < b.smallnumber) ^ a.isNegative;
    } else {
        return vec_less(*a.number, *b.number) ^ a.isNegative;
    }
}

bool operator>(big_integer const &a, big_integer const &b) {
    return b < a;
}

bool operator<=(big_integer const &a, big_integer const &b) {
    return !(a > b);
}

bool operator>=(big_integer const &a, big_integer const &b) {
    return b <= a;
}

std::string to_string(big_integer const &a) {
    if (a.isSmall) {
        return (a.isNegative ? "-" : "") + std::to_string(a.smallnumber);
    }

    std::vector<char> v;
    big_integer tmp(a);
    while (tmp != 0) {
        big_integer lst = tmp % 10;
        assert(lst.isSmall);
        v.push_back(static_cast<char>('0' + lst.smallnumber % 10));
        tmp /= 10;
    }

    std::string res;
    if (a.isNegative) {
        res = "-";
    }
    while (!v.empty()) {
        res += v.back();
        v.pop_back();
    }
    return res;
}

big_integer operator+(big_integer a, big_integer const &b) {
    return a += b;
}
big_integer operator-(big_integer a, big_integer const &b) {
    return a -= b;
}
big_integer operator*(big_integer a, big_integer const &b) {
    return a *= b;
}
big_integer operator/(big_integer a, big_integer const &b) {
    return a /= b;
}
big_integer operator%(big_integer a, big_integer const &b) {
    return a %= b;
}
big_integer operator*(big_integer a, int32_t b) {
    return a *= b;
}
big_integer operator*(int32_t a, big_integer b) {
    return b *= a;
}
big_integer operator*(big_integer a, uint32_t b) {
    return a *= b;
}
big_integer operator*(uint32_t a, big_integer b) {
    return b *= a;
}
big_integer operator&(big_integer a, big_integer const &b) {
    return a &= b;
}
big_integer operator|(big_integer a, big_integer const &b) {
    return a |= b;
}
big_integer operator^(big_integer a, big_integer const &b) {
    return a ^= b;
}
big_integer operator<<(big_integer a, int b) {
    return a <<= b;
}
big_integer operator>>(big_integer a, int b) {
    return a >>= b;
}

std::ostream &operator<<(std::ostream &s, big_integer const &a) {
    return s << to_string(a);
}

void big_integer::remove_leading_zeros() {
    if (isSmall) { return; }
    while (!number->empty() && number->back() == 0) {
        number->pop_back();
    }
    if (number->empty()) {
        to_small(0);
        isNegative = false;
    } else if (number->size() == 1) {
        to_small(number->back());
    }
}

void big_integer::to_big() {
    if (!isSmall) { return; }
    ui tmp = smallnumber;
    new(&number) std::shared_ptr<storage_t>();
    number = std::make_shared<storage_t>(1, tmp);
    isSmall = false;
}

void big_integer::to_big(uint64_t x) {
    assert(isSmall);
    if (isSmall) {
        new(&number) std::shared_ptr<storage_t>();
    }
    ui low = uicast(x);
    ui high = uicast(x >> BITS);
    number = std::make_shared<storage_t>(2);
    (*number)[0] = low;
    (*number)[1] = high;
    isSmall = false;
}

void big_integer::to_small() {
    if (isSmall) { return; }
    number.~shared_ptr();
    smallnumber = 0;
    isSmall = true;
}

void big_integer::to_small(uint32_t x) {
    assert(!isSmall);
    if (!isSmall) { number.~shared_ptr(); }
    smallnumber = x;
    isSmall = true;
}

void big_integer::make_unique_storage() {
    assert(!isSmall);
    if (isSmall) { return; }
    if (number.use_count() > 1) { number = std::make_shared<storage_t>(*number); }
}

uint64_t big_integer::toulong() const {
    assert(isSmall);
    return ullcast(smallnumber);
}

size_t big_integer::size() const {
    if (isSmall) {
        return smallnumber == 0 ? 0 : 1;
    }
    return number->size();
}

bool sign(ui x) {
    return (x >> 31) != 0;
}

std::vector<uint32_t> big_integer::to_complement() const {
    storage_t res;
    if (isSmall) {
        ull tmp = toulong();
        if (isNegative) { tmp = ~tmp + 1; }
        res = { uicast(tmp), uicast(tmp >> BITS) };
    } else {
        res = *number;

        if (isNegative) {
            res.push_back(0);
            ull carry = 1;
            for (auto &x : res) {
                ull tmp = ~x + carry;
                x = uicast(tmp);
                carry = tmp >> BITS;
            }
        }
    }
    return res;
}

void big_integer::from_complement(const std::vector<uint32_t> & vec) {
    if (vec.empty()) { to_small(0); }
    isNegative = sign(vec.back());

    to_big();
    number = std::make_shared<storage_t>(vec);
    if (isNegative) {
        number->push_back(getPadding(isNegative));

        ull carry = 1;
        for (auto &x : *number) {
            ull tmp = ~x + carry;
            x = uicast(tmp);
            carry = tmp >> BITS;
        }
    }

    remove_leading_zeros();
}

