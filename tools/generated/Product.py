from dataclasses import dataclass
from typing import Optional

@dataclass
class Product:
    id: str
    name: str
    price: int
