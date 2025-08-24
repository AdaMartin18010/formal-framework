# 功能模型DSL草案

## 1. 设计目标

- 用统一DSL描述业务逻辑、规则引擎、状态机、工作流等功能性组件
- 支持自动生成Spring Boot、Node.js、Python等主流框架的业务逻辑代码
- 提供形式化验证和自动化推理能力
- 支持多语言、多框架的代码生成
- 实现业务逻辑的自动优化和重构

## 2. 基本语法结构

### 2.1 业务逻辑建模 (Business Logic Modeling)

```dsl
business_logic OrderService {
  class: "com.example.OrderService"
  framework: "spring_boot"
  
  methods: [
    {
      name: "createOrder"
      description: "创建订单"
      parameters: [
        {
          name: "orderRequest"
          type: "OrderCreateRequest"
          validation: {
            required: true
            not_null: true
          }
        }
      ]
      logic: [
        {
          step: "validate_request"
          action: "validateOrderRequest"
          conditions: [
            {
              check: "orderRequest.items != null"
              message: "订单项不能为空"
            },
            {
              check: "orderRequest.items.size() > 0"
              message: "订单项数量必须大于0"
            }
          ]
        },
        {
          step: "check_inventory"
          action: "checkInventoryAvailability"
          service: "inventoryService"
          method: "checkStock"
          parameters: {
            items: "orderRequest.items"
          }
          error_handling: {
            exception: "InsufficientStockException"
            action: "throw_exception"
          }
        },
        {
          step: "calculate_total"
          action: "calculateOrderTotal"
          logic: [
            "sum = 0",
            "for item in orderRequest.items:",
            "  sum += item.price * item.quantity",
            "  if item.discount > 0:",
            "    sum -= item.discount",
            "return sum"
          ]
        },
        {
          step: "apply_discount"
          action: "applyDiscountRules"
          rules: [
            {
              condition: "orderTotal >= 1000"
              action: "apply 10% discount"
              calculation: "discount = orderTotal * 0.1"
            },
            {
              condition: "customer.isVip"
              action: "apply VIP discount"
              calculation: "discount += orderTotal * 0.05"
            }
          ]
        },
        {
          step: "create_order"
          action: "persistOrder"
          service: "orderRepository"
          method: "save"
          parameters: {
            order: "new Order(orderRequest, totalAmount, discount)"
          }
        },
        {
          step: "update_inventory"
          action: "updateInventory"
          service: "inventoryService"
          method: "reduceStock"
          parameters: {
            items: "orderRequest.items"
          }
        },
        {
          step: "send_notification"
          action: "notifyCustomer"
          service: "notificationService"
          method: "sendOrderConfirmation"
          parameters: {
            orderId: "order.id",
            customerEmail: "orderRequest.customerEmail"
          }
        }
      ]
      return_type: "OrderResponse"
      exceptions: [
        "ValidationException",
        "InsufficientStockException",
        "PaymentException"
      ]
    }
  ]
}
```

### 2.2 规则引擎建模 (Rule Engine Modeling)

```dsl
rule_engine PricingRuleEngine {
  framework: "drools"
  
  rules: [
    {
      name: "volume_discount_rule"
      description: "批量购买折扣规则"
      priority: 1
      when: [
        "order.totalAmount >= 1000",
        "order.customer.type == 'REGULAR'"
      ]
      then: [
        "order.discount = order.totalAmount * 0.1",
        "order.discountReason = 'Volume Discount'"
      ]
    },
    {
      name: "vip_customer_rule"
      description: "VIP客户折扣规则"
      priority: 2
      when: [
        "order.customer.type == 'VIP'",
        "order.customer.membershipYears >= 2"
      ]
      then: [
        "order.discount += order.totalAmount * 0.05",
        "order.discountReason += ', VIP Discount'"
      ]
    },
    {
      name: "seasonal_promotion_rule"
      description: "季节性促销规则"
      priority: 3
      when: [
        "currentDate.month == 12",
        "order.totalAmount >= 500"
      ]
      then: [
        "order.discount += order.totalAmount * 0.15",
        "order.discountReason += ', Holiday Promotion'"
      ]
    },
    {
      name: "new_customer_rule"
      description: "新客户优惠规则"
      priority: 4
      when: [
        "order.customer.registrationDate >= currentDate - 30",
        "order.totalAmount >= 200"
      ]
      then: [
        "order.discount += order.totalAmount * 0.08",
        "order.discountReason += ', New Customer Bonus'"
      ]
    }
  ]
  
  rule_chaining: {
    enabled: true
    max_iterations: 10
    conflict_resolution: "priority"
  }
  
  rule_monitoring: {
    enabled: true
    metrics: [
      "rule_execution_count",
      "rule_execution_time",
      "rule_activation_count"
    ]
  }
}
```

### 2.3 状态机建模 (State Machine Modeling)

```dsl
state_machine OrderStateMachine {
  framework: "spring_statemachine"
  
  states: [
    {
      name: "CREATED"
      description: "订单已创建"
      entry_actions: [
        "sendOrderCreatedNotification"
      ]
    },
    {
      name: "PAYMENT_PENDING"
      description: "等待支付"
      entry_actions: [
        "sendPaymentReminder"
      ],
      exit_actions: [
        "cancelPaymentReminder"
      ]
    },
    {
      name: "PAID"
      description: "已支付"
      entry_actions: [
        "processPayment",
        "updateInventory"
      ]
    },
    {
      name: "PROCESSING"
      description: "处理中"
      entry_actions: [
        "assignToWarehouse"
      ]
    },
    {
      name: "SHIPPED"
      description: "已发货"
      entry_actions: [
        "generateTrackingNumber",
        "sendShippingNotification"
      ]
    },
    {
      name: "DELIVERED"
      description: "已送达"
      entry_actions: [
        "sendDeliveryConfirmation",
        "requestReview"
      ]
    },
    {
      name: "CANCELLED"
      description: "已取消"
      entry_actions: [
        "processRefund",
        "restoreInventory",
        "sendCancellationNotification"
      ]
    }
  ]
  
  transitions: [
    {
      from: "CREATED"
      to: "PAYMENT_PENDING"
      event: "SUBMIT_ORDER"
      guard: "orderValidationPassed"
    },
    {
      from: "PAYMENT_PENDING"
      to: "PAID"
      event: "PAYMENT_RECEIVED"
      guard: "paymentValidationPassed"
    },
    {
      from: "PAYMENT_PENDING"
      to: "CANCELLED"
      event: "PAYMENT_TIMEOUT"
      guard: "paymentTimeoutReached"
    },
    {
      from: "PAID"
      to: "PROCESSING"
      event: "START_PROCESSING"
      guard: "inventoryAvailable"
    },
    {
      from: "PROCESSING"
      to: "SHIPPED"
      event: "SHIP_ORDER"
      guard: "orderReadyForShipping"
    },
    {
      from: "SHIPPED"
      to: "DELIVERED"
      event: "CONFIRM_DELIVERY"
      guard: "deliveryConfirmed"
    },
    {
      from: ["CREATED", "PAYMENT_PENDING", "PAID"]
      to: "CANCELLED"
      event: "CANCEL_ORDER"
      guard: "orderCancellable"
    }
  ]
  
  guards: [
    {
      name: "orderValidationPassed"
      logic: [
        "return order.items != null && order.items.size() > 0",
        "&& order.customer != null",
        "&& order.shippingAddress != null"
      ]
    },
    {
      name: "paymentValidationPassed"
      logic: [
        "return payment.amount == order.totalAmount",
        "&& payment.status == 'SUCCESS'",
        "&& payment.method != null"
      ]
    },
    {
      name: "inventoryAvailable"
      logic: [
        "for item in order.items:",
        "  if inventoryService.getStock(item.productId) < item.quantity:",
        "    return false",
        "return true"
      ]
    }
  ]
  
  actions: [
    {
      name: "sendOrderCreatedNotification"
      service: "notificationService"
      method: "sendOrderCreated"
      parameters: {
        orderId: "order.id",
        customerEmail: "order.customer.email"
      }
    },
    {
      name: "processPayment"
      service: "paymentService"
      method: "processPayment"
      parameters: {
        orderId: "order.id",
        amount: "order.totalAmount",
        method: "order.paymentMethod"
      }
    }
  ]
}
```

### 2.4 工作流建模 (Workflow Modeling)

```dsl
workflow OrderProcessingWorkflow {
  framework: "camunda"
  
  process: {
    id: "order-processing"
    name: "订单处理工作流"
    version: "1.0"
  }
  
  tasks: [
    {
      name: "validate_order"
      type: "user_task"
      assignee: "order_validator"
      description: "验证订单信息"
      form: {
        fields: [
          {
            name: "orderValid"
            type: "boolean"
            label: "订单是否有效"
          },
          {
            name: "validationNotes"
            type: "text"
            label: "验证备注"
          }
        ]
      }
      outcomes: [
        {
          condition: "orderValid == true"
          next: "check_inventory"
        },
        {
          condition: "orderValid == false"
          next: "reject_order"
        }
      ]
    },
    {
      name: "check_inventory"
      type: "service_task"
      service: "inventoryService"
      method: "checkAvailability"
      input_parameters: {
        items: "order.items"
      }
      output_parameters: {
        available: "inventoryResult.available"
        unavailableItems: "inventoryResult.unavailableItems"
      }
      outcomes: [
        {
          condition: "available == true"
          next: "process_payment"
        },
        {
          condition: "available == false"
          next: "notify_out_of_stock"
        }
      ]
    },
    {
      name: "process_payment"
      type: "service_task"
      service: "paymentService"
      method: "processPayment"
      input_parameters: {
        orderId: "order.id"
        amount: "order.totalAmount"
        method: "order.paymentMethod"
      }
      output_parameters: {
        paymentStatus: "paymentResult.status"
        transactionId: "paymentResult.transactionId"
      }
      outcomes: [
        {
          condition: "paymentStatus == 'SUCCESS'"
          next: "prepare_shipment"
        },
        {
          condition: "paymentStatus == 'FAILED'"
          next: "handle_payment_failure"
        }
      ]
    },
    {
      name: "prepare_shipment"
      type: "user_task"
      assignee: "warehouse_staff"
      description: "准备发货"
      form: {
        fields: [
          {
            name: "packagingComplete"
            type: "boolean"
            label: "包装完成"
          },
          {
            name: "trackingNumber"
            type: "text"
            label: "跟踪号"
          }
        ]
      }
      outcomes: [
        {
          condition: "packagingComplete == true"
          next: "ship_order"
        }
      ]
    },
    {
      name: "ship_order"
      type: "service_task"
      service: "shippingService"
      method: "shipOrder"
      input_parameters: {
        orderId: "order.id"
        trackingNumber: "trackingNumber"
        shippingAddress: "order.shippingAddress"
      }
      outcomes: [
        {
          condition: "true"
          next: "complete_order"
        }
      ]
    }
  ]
  
  events: [
    {
      name: "order_created"
      type: "start_event"
      trigger: "message"
      message_name: "OrderCreated"
    },
    {
      name: "order_completed"
      type: "end_event"
      trigger: "message"
      message_name: "OrderCompleted"
    },
    {
      name: "payment_timeout"
      type: "intermediate_event"
      trigger: "timer"
      timer_definition: "PT24H"
    }
  ]
  
  variables: [
    {
      name: "order"
      type: "Order"
      scope: "process"
    },
    {
      name: "paymentResult"
      type: "PaymentResult"
      scope: "process"
    },
    {
      name: "inventoryResult"
      type: "InventoryResult"
      scope: "process"
    }
  ]
}
```

## 3. 高级特性

### 3.1 业务规则模板 (Business Rule Templates)

```dsl
business_rule_template DiscountRuleTemplate {
  category: "pricing"
  
  parameters: [
    {
      name: "threshold"
      type: "decimal"
      description: "折扣阈值"
    },
    {
      name: "discount_percentage"
      type: "decimal"
      description: "折扣百分比"
    },
    {
      name: "customer_type"
      type: "string"
      description: "客户类型"
    }
  ]
  
  template: {
    name: "{{customer_type}}_discount_rule"
    description: "{{customer_type}}客户折扣规则"
    when: [
      "order.totalAmount >= {{threshold}}",
      "order.customer.type == '{{customer_type}}'"
    ]
    then: [
      "order.discount += order.totalAmount * {{discount_percentage}}",
      "order.discountReason += ', {{customer_type}} Discount'"
    ]
  }
  
  instances: [
    {
      name: "vip_discount"
      parameters: {
        threshold: 1000
        discount_percentage: 0.1
        customer_type: "VIP"
      }
    },
    {
      name: "regular_discount"
      parameters: {
        threshold: 500
        discount_percentage: 0.05
        customer_type: "REGULAR"
      }
    }
  ]
}
```

### 3.2 决策表 (Decision Tables)

```dsl
decision_table ShippingDecisionTable {
  name: "运费计算决策表"
  
  input_columns: [
    {
      name: "order_total"
      type: "decimal"
      description: "订单总额"
    },
    {
      name: "shipping_zone"
      type: "string"
      description: "配送区域"
    },
    {
      name: "customer_type"
      type: "string"
      description: "客户类型"
    }
  ]
  
  output_columns: [
    {
      name: "shipping_cost"
      type: "decimal"
      description: "运费"
    },
    {
      name: "shipping_method"
      type: "string"
      description: "配送方式"
    }
  ]
  
  rules: [
    {
      conditions: {
        order_total: ">= 1000"
        shipping_zone: "LOCAL"
        customer_type: "VIP"
      }
      outputs: {
        shipping_cost: 0
        shipping_method: "FREE_EXPRESS"
      }
    },
    {
      conditions: {
        order_total: ">= 500"
        shipping_zone: "LOCAL"
        customer_type: "REGULAR"
      }
      outputs: {
        shipping_cost: 10
        shipping_method: "STANDARD"
      }
    },
    {
      conditions: {
        order_total: "< 500"
        shipping_zone: "LOCAL"
        customer_type: "REGULAR"
      }
      outputs: {
        shipping_cost: 20
        shipping_method: "STANDARD"
      }
    },
    {
      conditions: {
        order_total: ">= 1000"
        shipping_zone: "INTERNATIONAL"
        customer_type: "VIP"
      }
      outputs: {
        shipping_cost: 50
        shipping_method: "EXPRESS"
      }
    }
  ]
}
```

### 3.3 业务函数库 (Business Function Library)

```dsl
business_function_library OrderFunctions {
  functions: [
    {
      name: "calculateOrderTotal"
      description: "计算订单总额"
      parameters: [
        {
          name: "items"
          type: "List<OrderItem>"
        }
      ]
      return_type: "decimal"
      implementation: [
        "total = 0",
        "for item in items:",
        "  total += item.price * item.quantity",
        "  if item.discount > 0:",
        "    total -= item.discount",
        "return total"
      ]
    },
    {
      name: "applyDiscountRules"
      description: "应用折扣规则"
      parameters: [
        {
          name: "order"
          type: "Order"
        },
        {
          name: "rules"
          type: "List<DiscountRule>"
        }
      ]
      return_type: "decimal"
      implementation: [
        "totalDiscount = 0",
        "for rule in rules:",
        "  if rule.evaluate(order):",
        "    discount = rule.calculateDiscount(order)",
        "    totalDiscount += discount",
        "return totalDiscount"
      ]
    },
    {
      name: "validateOrderRequest"
      description: "验证订单请求"
      parameters: [
        {
          name: "request"
          type: "OrderCreateRequest"
        }
      ]
      return_type: "ValidationResult"
      implementation: [
        "errors = []",
        "if request.items == null or request.items.isEmpty():",
        "  errors.add('订单项不能为空')",
        "if request.customer == null:",
        "  errors.add('客户信息不能为空')",
        "if request.shippingAddress == null:",
        "  errors.add('配送地址不能为空')",
        "return new ValidationResult(errors.isEmpty(), errors)"
      ]
    }
  ]
}
```

## 4. 自动化代码生成

### 4.1 Java Spring Boot 生成

```dsl
generate_java OrderService {
  framework: "spring_boot"
  patterns: [
    "business_logic",
    "rule_engine"
  ]
  output: {
    directory: "src/main/java"
    package: "com.example.orderservice"
  }
}
```

生成的代码示例：

```java
@Service
@Transactional
public class OrderService {
    
    @Autowired
    private OrderRepository orderRepository;
    
    @Autowired
    private InventoryService inventoryService;
    
    @Autowired
    private PaymentService paymentService;
    
    @Autowired
    private NotificationService notificationService;
    
    @Autowired
    private KieSession kieSession;
    
    public OrderResponse createOrder(OrderCreateRequest request) {
        // 验证请求
        ValidationResult validation = validateOrderRequest(request);
        if (!validation.isValid()) {
            throw new ValidationException(validation.getErrors());
        }
        
        // 检查库存
        InventoryResult inventory = inventoryService.checkStock(request.getItems());
        if (!inventory.isAvailable()) {
            throw new InsufficientStockException(inventory.getUnavailableItems());
        }
        
        // 计算总额
        BigDecimal totalAmount = calculateOrderTotal(request.getItems());
        
        // 应用折扣规则
        Order order = new Order(request, totalAmount);
        kieSession.insert(order);
        kieSession.fireAllRules();
        kieSession.dispose();
        
        // 保存订单
        Order savedOrder = orderRepository.save(order);
        
        // 更新库存
        inventoryService.reduceStock(request.getItems());
        
        // 发送通知
        notificationService.sendOrderConfirmation(savedOrder.getId(), request.getCustomerEmail());
        
        return new OrderResponse(savedOrder);
    }
    
    private ValidationResult validateOrderRequest(OrderCreateRequest request) {
        List<String> errors = new ArrayList<>();
        
        if (request.getItems() == null || request.getItems().isEmpty()) {
            errors.add("订单项不能为空");
        }
        if (request.getCustomer() == null) {
            errors.add("客户信息不能为空");
        }
        if (request.getShippingAddress() == null) {
            errors.add("配送地址不能为空");
        }
        
        return new ValidationResult(errors.isEmpty(), errors);
    }
    
    private BigDecimal calculateOrderTotal(List<OrderItem> items) {
        return items.stream()
            .map(item -> item.getPrice().multiply(BigDecimal.valueOf(item.getQuantity()))
                .subtract(item.getDiscount() != null ? item.getDiscount() : BigDecimal.ZERO))
            .reduce(BigDecimal.ZERO, BigDecimal::add);
    }
}
```

### 4.2 Python Django 生成

```dsl
generate_python OrderService {
  framework: "django"
  patterns: [
    "business_logic",
    "state_machine"
  ]
  output: {
    directory: "orders"
    app_name: "orders"
  }
}
```

生成的代码示例：

```python
from django.db import models
from django.core.exceptions import ValidationError
from django_fsm import FSMField, transition
from decimal import Decimal

class Order(models.Model):
    CREATED = 'created'
    PAYMENT_PENDING = 'payment_pending'
    PAID = 'paid'
    PROCESSING = 'processing'
    SHIPPED = 'shipped'
    DELIVERED = 'delivered'
    CANCELLED = 'cancelled'
    
    STATE_CHOICES = [
        (CREATED, '已创建'),
        (PAYMENT_PENDING, '等待支付'),
        (PAID, '已支付'),
        (PROCESSING, '处理中'),
        (SHIPPED, '已发货'),
        (DELIVERED, '已送达'),
        (CANCELLED, '已取消'),
    ]
    
    state = FSMField(default=CREATED, choices=STATE_CHOICES)
    customer = models.ForeignKey('Customer', on_delete=models.CASCADE)
    total_amount = models.DecimalField(max_digits=10, decimal_places=2)
    discount = models.DecimalField(max_digits=10, decimal_places=2, default=0)
    
    @transition(field=state, source=CREATED, target=PAYMENT_PENDING)
    def submit_order(self):
        """提交订单"""
        self.validate_order()
        self.send_order_created_notification()
    
    @transition(field=state, source=PAYMENT_PENDING, target=PAID)
    def receive_payment(self):
        """收到支付"""
        self.process_payment()
        self.update_inventory()
    
    @transition(field=state, source=PAID, target=PROCESSING)
    def start_processing(self):
        """开始处理"""
        self.assign_to_warehouse()
    
    def validate_order(self):
        """验证订单"""
        if not self.items.exists():
            raise ValidationError("订单项不能为空")
        if not self.customer:
            raise ValidationError("客户信息不能为空")
    
    def calculate_total(self):
        """计算订单总额"""
        total = sum(item.price * item.quantity for item in self.items.all())
        self.apply_discount_rules(total)
        return total
    
    def apply_discount_rules(self, total):
        """应用折扣规则"""
        discount = Decimal('0')
        
        # 批量折扣
        if total >= 1000:
            discount += total * Decimal('0.1')
        
        # VIP折扣
        if self.customer.type == 'VIP':
            discount += total * Decimal('0.05')
        
        self.discount = discount
        self.total_amount = total - discount
```

### 4.3 Node.js Express 生成

```dsl
generate_nodejs OrderService {
  framework: "express"
  patterns: [
    "business_logic",
    "workflow"
  ]
  output: {
    directory: "src/services"
    module: "order-service"
  }
}
```

生成的代码示例：

```javascript
const { ValidationError, InsufficientStockError } = require('../errors');
const OrderRepository = require('../repositories/order-repository');
const InventoryService = require('./inventory-service');
const PaymentService = require('./payment-service');
const NotificationService = require('./notification-service');

class OrderService {
    constructor() {
        this.orderRepository = new OrderRepository();
        this.inventoryService = new InventoryService();
        this.paymentService = new PaymentService();
        this.notificationService = new NotificationService();
    }
    
    async createOrder(orderRequest) {
        try {
            // 验证请求
            const validation = this.validateOrderRequest(orderRequest);
            if (!validation.isValid) {
                throw new ValidationError(validation.errors);
            }
            
            // 检查库存
            const inventory = await this.inventoryService.checkStock(orderRequest.items);
            if (!inventory.available) {
                throw new InsufficientStockError(inventory.unavailableItems);
            }
            
            // 计算总额
            const totalAmount = this.calculateOrderTotal(orderRequest.items);
            
            // 应用折扣规则
            const discount = this.applyDiscountRules(orderRequest, totalAmount);
            const finalAmount = totalAmount - discount;
            
            // 创建订单
            const order = await this.orderRepository.create({
                ...orderRequest,
                totalAmount: finalAmount,
                discount: discount
            });
            
            // 更新库存
            await this.inventoryService.reduceStock(orderRequest.items);
            
            // 发送通知
            await this.notificationService.sendOrderConfirmation(
                order.id, 
                orderRequest.customerEmail
            );
            
            return {
                success: true,
                orderId: order.id,
                totalAmount: finalAmount,
                discount: discount
            };
        } catch (error) {
            throw error;
        }
    }
    
    validateOrderRequest(request) {
        const errors = [];
        
        if (!request.items || request.items.length === 0) {
            errors.push('订单项不能为空');
        }
        if (!request.customer) {
            errors.push('客户信息不能为空');
        }
        if (!request.shippingAddress) {
            errors.push('配送地址不能为空');
        }
        
        return {
            isValid: errors.length === 0,
            errors: errors
        };
    }
    
    calculateOrderTotal(items) {
        return items.reduce((total, item) => {
            const itemTotal = item.price * item.quantity;
            const discount = item.discount || 0;
            return total + itemTotal - discount;
        }, 0);
    }
    
    applyDiscountRules(request, totalAmount) {
        let discount = 0;
        
        // 批量折扣
        if (totalAmount >= 1000) {
            discount += totalAmount * 0.1;
        }
        
        // VIP折扣
        if (request.customer.type === 'VIP') {
            discount += totalAmount * 0.05;
        }
        
        return discount;
    }
}

module.exports = OrderService;
```

## 5. 形式化验证

### 5.1 业务逻辑验证

```dsl
verify_business_logic OrderService {
  properties: [
    "order_validation_completeness",
    "discount_calculation_accuracy",
    "inventory_consistency"
  ]
  constraints: {
    max_discount_percentage: 0.5
    min_order_amount: 0.01
    max_order_items: 100
  }
  scenarios: [
    "normal_order_flow",
    "discount_edge_cases",
    "inventory_shortage"
  ]
}
```

### 5.2 状态机验证

```dsl
verify_state_machine OrderStateMachine {
  properties: [
    "state_transition_validity",
    "deadlock_freedom",
    "liveness_property"
  ]
  constraints: {
    max_transition_time: "30s"
    min_state_duration: "1s"
  }
  scenarios: [
    "normal_flow",
    "cancellation_flow",
    "payment_failure_flow"
  ]
}
```

## 6. 监控和可观测性

### 6.1 业务指标定义

```dsl
business_metrics OrderService {
  operational: {
    orders_created: "counter"
    orders_processed: "counter"
    average_processing_time: "histogram"
    error_rate: "gauge"
  }
  business: {
    total_revenue: "counter"
    average_order_value: "gauge"
    customer_satisfaction: "gauge"
    discount_utilization: "gauge"
  }
  performance: {
    rule_engine_execution_time: "histogram"
    state_transition_time: "histogram"
    workflow_completion_time: "histogram"
  }
}
```

### 6.2 告警规则

```dsl
business_alerts OrderService {
  high_error_rate: {
    condition: "error_rate > 0.05"
    duration: "5m"
    severity: "warning"
  }
  low_processing_throughput: {
    condition: "orders_processed_per_minute < 10"
    duration: "10m"
    severity: "critical"
  }
  excessive_discount_usage: {
    condition: "discount_utilization > 0.8"
    duration: "1h"
    severity: "warning"
  }
}
```

## 7. 最佳实践和模式组合

### 7.1 领域驱动设计 (DDD)

```dsl
ddd_pattern OrderDomain {
  aggregates: [
    {
      name: "Order"
      entities: ["Order", "OrderItem"]
      value_objects: ["Money", "Address"]
      repositories: ["OrderRepository"]
    },
    {
      name: "Customer"
      entities: ["Customer"]
      value_objects: ["Email", "Phone"]
      repositories: ["CustomerRepository"]
    }
  ]
  
  services: [
    {
      name: "OrderService"
      type: "domain_service"
      responsibilities: ["order_creation", "discount_calculation"]
    },
    {
      name: "PricingService"
      type: "domain_service"
      responsibilities: ["price_calculation", "discount_application"]
    }
  ]
  
  events: [
    {
      name: "OrderCreated"
      publisher: "Order"
      subscribers: ["InventoryService", "NotificationService"]
    },
    {
      name: "OrderPaid"
      publisher: "Order"
      subscribers: ["ShippingService", "AnalyticsService"]
    }
  ]
}
```

### 7.2 事件溯源 (Event Sourcing)

```dsl
event_sourcing_pattern OrderEventSourcing {
  events: [
    {
      name: "OrderCreated"
      data: {
        orderId: "string"
        customerId: "string"
        items: "OrderItem[]"
        totalAmount: "decimal"
      }
    },
    {
      name: "OrderItemAdded"
      data: {
        orderId: "string"
        item: "OrderItem"
      }
    },
    {
      name: "DiscountApplied"
      data: {
        orderId: "string"
        discountAmount: "decimal"
        reason: "string"
      }
    },
    {
      name: "OrderPaid"
      data: {
        orderId: "string"
        paymentMethod: "string"
        transactionId: "string"
      }
    }
  ]
  
  projections: [
    {
      name: "OrderSummary"
      events: ["OrderCreated", "OrderItemAdded", "DiscountApplied", "OrderPaid"]
      state: {
        orderId: "string"
        status: "string"
        totalAmount: "decimal"
        discountAmount: "decimal"
        paidAmount: "decimal"
      }
    }
  ]
  
  snapshots: {
    enabled: true
    interval: 100
    strategy: "full_state"
  }
}
```

这个扩展后的功能模型DSL提供了：

1. **详细的语法定义**：涵盖业务逻辑、规则引擎、状态机、工作流等核心模式
2. **高级特性**：业务规则模板、决策表、业务函数库
3. **自动化代码生成**：支持Java、Python、Node.js等多语言框架
4. **形式化验证**：提供属性验证和约束检查
5. **监控和可观测性**：业务指标定义和告警规则
6. **最佳实践**：领域驱动设计和事件溯源模式
7. **标准映射**：与主流框架和模式对接
8. **递归扩展**：支持复杂的业务逻辑组合和优化
