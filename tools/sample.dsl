model SampleSystem: business_model {
    entity Customer {
        id: string;
        name: string;
        email: string;
    }

    entity Product {
        id: string;
        name: string;
        price: number;
    }

    operation createCustomer(name: string, email: string) -> Customer;
    operation createProduct(name: string, price: number) -> Product;
}
