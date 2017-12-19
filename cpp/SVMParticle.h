#ifndef DZNL_SVMPARTICLE_H
#define DZNL_SVMPARTICLE_H

#include <string>
#include <tuple>

namespace dznl {

    struct SVMParticle {

        std::string type;
        double mass;
        double charge;

        bool operator==(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) ==
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

        bool operator!=(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) !=
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

        bool operator<(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) <
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

        bool operator<=(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) <=
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

        bool operator>(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) >
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

        bool operator>=(const SVMParticle &rhs) const {
            return std::tie(type, mass, charge) >=
                   std::tie(rhs.type, rhs.mass, rhs.charge);
        }

    }; // struct SVMParticle

} // namespace dznl

#endif // DZNL_SVMPARTICLE_H
